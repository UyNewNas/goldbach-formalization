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

namespace SimplicesBlock052

noncomputable def fragment0400698Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0400698Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0400698Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '2'])
noncomputable def fragment0400698Acc00100 : List (String × SourceJson) := (fragment0400698Field000Key00, fragment0400698Field000Value00) :: fragment0400698Acc00000
noncomputable def fragment0400698Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '2', ',']

theorem object_fragment0400698_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0400698Field000Chars00 ++ tail)) fragment0400698Acc00000 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0400698Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_000"
  err.flush

noncomputable def fragment0400698Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0400698Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0400698Acc00200 : List (String × SourceJson) := (fragment0400698Field001Key00, fragment0400698Field001Value00) :: fragment0400698Acc00100
noncomputable def fragment0400698Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0400698_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0400698Field001Chars00 ++ tail)) fragment0400698Acc00100 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0400698Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_001"
  err.flush

noncomputable def fragment0400698Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0400698Field002Value00 : SourceJson := .str (String.ofList ['3', '4', '2', '3', '5', '6', '2', '8', '0', '1', '0', '6', '2', '0', '1', '0', '2', '0', '6', '0', '2', '0', '7', '1', '1', '5', '6', '7', '6', '8', '7', '4', '7', '4', '1', '3', '4', '1', '8', '7', '/', '8', '0', '0', '9', '5', '9', '5', '1', '2', '0', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0400698Acc00300 : List (String × SourceJson) := (fragment0400698Field002Key00, fragment0400698Field002Value00) :: fragment0400698Acc00200
noncomputable def fragment0400698Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '4', '2', '3', '5', '6', '2', '8', '0', '1', '0', '6', '2', '0', '1', '0', '2', '0', '6', '0', '2', '0', '7', '1', '1', '5', '6', '7', '6', '8', '7', '4', '7', '4', '1', '3', '4', '1', '8', '7', '/', '8', '0', '0', '9', '5', '9', '5', '1', '2', '0', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0400698_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0400698Field002Chars00 ++ tail)) fragment0400698Acc00200 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0400698Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_002"
  err.flush

noncomputable def fragment0400698Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0400698Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0400698Acc00400 : List (String × SourceJson) := (fragment0400698Field003Key00, fragment0400698Field003Value00) :: fragment0400698Acc00300
noncomputable def fragment0400698Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0400698_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0400698Field003Chars00 ++ tail)) fragment0400698Acc00300 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0400698Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_003"
  err.flush

noncomputable def fragment0400698Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0400698Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '6', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0400698Acc00500 : List (String × SourceJson) := (fragment0400698Field004Key00, fragment0400698Field004Value00) :: fragment0400698Acc00400
noncomputable def fragment0400698Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '6', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0400698_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0400698Field004Chars00 ++ tail)) fragment0400698Acc00400 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0400698Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_004"
  err.flush

noncomputable def fragment0400698Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0400698Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '6', '5', '6', '9', '1', '9', '7', '8', '3', '/', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '9', '9', '0', '2', '4', '3', '5', '6', '1', '/', '3', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '1', '7', '3', '5', '2', '9', '3', '4', '6', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '2', '2', '3', '0', '8', '4', '4', '7', '/', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '9', '6', '1', '0', '7', '7', '1', '2', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '3', '4', '6', '5', '1', '4', '8', '8', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '4', '8', '8', '5', '1', '2', '0', '1', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '8', '7', '3', '5', '5', '1', '6', '9', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '8', '7', '3', '1', '0', '4', '8', '1', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '9', '9', '2', '9', '3', '6', '0', '6', '3', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0400698Acc00600 : List (String × SourceJson) := (fragment0400698Field005Key00, fragment0400698Field005Value00) :: fragment0400698Acc00500
noncomputable def fragment0400698Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '5', '6', '9', '1', '9', '7', '8', '3', '/', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '9', '0', '2', '4', '3', '5', '6', '1', '/', '3', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '1', '7', '3', '5', '2', '9', '3', '4', '6', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '2', '2', '3', '0', '8', '4', '4', '7', '/', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '9', '6', '1', '0', '7', '7', '1', '2', '9', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '3', '4', '6', '5', '1', '4', '8', '8', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '4', '8', '8', '5', '1', '2', '0', '1', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '8', '7', '3', '5', '5', '1', '6', '9', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '8', '7', '3', '1', '0', '4', '8', '1', '/', '6', '7', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '9', '9', '2', '9', '3', '6', '0', '6', '3', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0400698_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0400698Field005Chars00 ++ tail)) fragment0400698Acc00500 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0400698Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_005"
  err.flush

noncomputable def fragment0400698Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0400698Field006Value00 : SourceJson := .str (String.ofList ['8', '6', '1', '9', '1', '9', '4', '9', '1', '7', '2', '7', '8', '1', '3', '7', '3', '6', '1', '2', '3', '0', '4', '1', '9', '5', '9', '7', '0', '2', '5', '0', '3', '6', '4', '4', '1', '6', '9', '0', '6', '0', '0', '9', '6', '0', '0', '0', '0', '/', '4', '1', '5', '3', '7', '2', '3', '9', '3', '5', '9', '7', '2', '9', '5', '8', '0', '4', '9', '0', '7', '1', '9', '3', '6', '1', '9', '2', '1', '3', '8', '2', '6', '9', '0', '2', '0', '5', '8', '9', '1', '3', '7', '2', '9', '6', '0', '3', '7', '7', '4', '4', '0', '7', '9', '5', '7', '6', '9', '3', '3', '4', '7', '7'])
noncomputable def fragment0400698Acc00700 : List (String × SourceJson) := (fragment0400698Field006Key00, fragment0400698Field006Value00) :: fragment0400698Acc00600
noncomputable def fragment0400698Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '6', '1', '9', '1', '9', '4', '9', '1', '7', '2', '7', '8', '1', '3', '7', '3', '6', '1', '2', '3', '0', '4', '1', '9', '5', '9', '7', '0', '2', '5', '0', '3', '6', '4', '4', '1', '6', '9', '0', '6', '0', '0', '9', '6', '0', '0', '0', '0', '/', '4', '1', '5', '3', '7', '2', '3', '9', '3', '5', '9', '7', '2', '9', '5', '8', '0', '4', '9', '0', '7', '1', '9', '3', '6', '1', '9', '2', '1', '3', '8', '2', '6', '9', '0', '2', '0', '5', '8', '9', '1', '3', '7', '2', '9', '6', '0', '3', '7', '7', '4', '4', '0', '7', '9', '5', '7', '6', '9', '3', '3', '4', '7', '7', '"', ',']

theorem object_fragment0400698_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0400698Field006Chars00 ++ tail)) fragment0400698Acc00600 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0400698Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_006"
  err.flush

noncomputable def fragment0400698Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0400698Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '0', '4', '4', '5', '1', '0', '5', '2', '6', '2', '9', '2', '3', '3', '1', '1', '0', '7', '7', '4', '4', '7', '6', '6', '5', '5', '1', '8', '8', '5', '6', '5', '2', '7', '6', '6', '5', '2', '0', '8', '2', '4', '9', '2', '3', '5', '9', '6', '5', '9', '7', '6', '3', '7', '9', '9', '3', '0', '3', '7', '9', '8', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '4', '5', '6', '4', '4', '2', '9', '8', '3', '1', '8', '4', '8', '3', '7', '9', '6', '7', '4', '4', '4', '2', '7', '2', '4', '9', '5', '4', '8', '3', '8', '9', '3', '2', '1', '1', '5', '0', '4', '0', '6', '9', '7', '1', '5', '2', '5', '4', '9', '5', '7', '9', '8', '8', '4', '8', '4', '3', '1', '4', '7', '4', '6', '2', '2', '4', '8', '7', '5', '5', '9', '9', '4', '6', '9', '4', '0', '4', '8', '5', '6', '2', '8', '3', '9', '0', '6', '8', '7', '6', '7', '7', '4', '6', '1', '5', '1', '9', '8', '0', '0', '1'])
noncomputable def fragment0400698Acc00800 : List (String × SourceJson) := (fragment0400698Field007Key00, fragment0400698Field007Value00) :: fragment0400698Acc00700
noncomputable def fragment0400698Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '0', '4', '4', '5', '1', '0', '5', '2', '6', '2', '9', '2', '3', '3', '1', '1', '0', '7', '7', '4', '4', '7', '6', '6', '5', '5', '1', '8', '8', '5', '6', '5', '2', '7', '6', '6', '5', '2', '0', '8', '2', '4', '9', '2', '3', '5', '9', '6', '5', '9', '7', '6', '3', '7', '9', '9', '3', '0', '3', '7', '9', '8', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '4', '5', '6', '4', '4', '2', '9', '8', '3', '1', '8', '4', '8', '3', '7', '9', '6', '7', '4', '4', '4', '2', '7', '2', '4', '9', '5', '4', '8', '3', '8', '9', '3', '2', '1', '1', '5', '0', '4', '0', '6', '9', '7', '1', '5', '2', '5', '4', '9', '5', '7', '9', '8', '8', '4', '8', '4', '3', '1', '4', '7', '4', '6', '2', '2', '4', '8', '7', '5', '5', '9', '9', '4', '6', '9', '4', '0', '4', '8', '5', '6', '2', '8', '3', '9', '0', '6', '8', '7', '6', '7', '7', '4', '6', '1', '5', '1', '9', '8', '0', '0', '1', '"', ',']

theorem object_fragment0400698_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0400698Field007Chars00 ++ tail)) fragment0400698Acc00700 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0400698Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_007"
  err.flush

noncomputable def fragment0400698Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0400698Field008Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '4', '0', '2', '5', '9', '0', '5', '8', '4', '8', '4', '5'])
noncomputable def fragment0400698Acc00900 : List (String × SourceJson) := (fragment0400698Field008Key00, fragment0400698Field008Value00) :: fragment0400698Acc00800
noncomputable def fragment0400698Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '4', '4', '0', '2', '5', '9', '0', '5', '8', '4', '8', '4', '5', '"', ',']

theorem object_fragment0400698_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0400698Field008Chars00 ++ tail)) fragment0400698Acc00800 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0400698Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_008"
  err.flush

noncomputable def fragment0400698Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0400698Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '3', '2', '5', '7', '9', '7', '8', '8', '0', '1', '3', '1', '9', '9'])
noncomputable def fragment0400698Acc01000 : List (String × SourceJson) := (fragment0400698Field009Key00, fragment0400698Field009Value00) :: fragment0400698Acc00900
noncomputable def fragment0400698Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '3', '2', '5', '7', '9', '7', '8', '8', '0', '1', '3', '1', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0400698_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0400698Field009Chars00 ++ tail)) fragment0400698Acc00900 =
      .ok (.obj (fragment0400698Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0400698_object_field_009"
  err.flush

noncomputable def fragment0400698Chars : List Char := '{' :: (fragment0400698Field000Chars00 ++ fragment0400698Field001Chars00 ++ fragment0400698Field002Chars00 ++ fragment0400698Field003Chars00 ++ fragment0400698Field004Chars00 ++ fragment0400698Field005Chars00 ++ fragment0400698Field006Chars00 ++ fragment0400698Field007Chars00 ++ fragment0400698Field008Chars00 ++ fragment0400698Field009Chars00)
noncomputable def fragment0400698Value : SourceJson := .obj (fragment0400698Acc01000.reverse)

theorem value_fragment0400698 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 205) (fragment0400698Chars ++ tail) =
      .ok (fragment0400698Value, tail) := by
  have hinput : fragment0400698Chars ++ tail = '{' :: (fragment0400698Field000Chars00 ++ (fragment0400698Field001Chars00 ++ (fragment0400698Field002Chars00 ++ (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0400698Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 205) (fragment0400698Chars ++ tail) =
        SourceJson.value (fuel + 205) ('{' :: (fragment0400698Field000Chars00 ++ (fragment0400698Field001Chars00 ++ (fragment0400698Field002Chars00 ++ (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 205)) hinput
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0400698Field000Chars00 ++ (fragment0400698Field001Chars00 ++ (fragment0400698Field002Chars00 ++ (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))))))))) fragment0400698Acc00000 := by rfl
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0400698Field001Chars00 ++ (fragment0400698Field002Chars00 ++ (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))))))))) fragment0400698Acc00100 := object_fragment0400698_field_000 fuel (fragment0400698Field001Chars00 ++ (fragment0400698Field002Chars00 ++ (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0400698Field002Chars00 ++ (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))))))) fragment0400698Acc00200 := object_fragment0400698_field_001 fuel (fragment0400698Field002Chars00 ++ (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))))))) fragment0400698Acc00300 := object_fragment0400698_field_002 fuel (fragment0400698Field003Chars00 ++ (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))))) fragment0400698Acc00400 := object_fragment0400698_field_003 fuel (fragment0400698Field004Chars00 ++ (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))))) fragment0400698Acc00500 := object_fragment0400698_field_004 fuel (fragment0400698Field005Chars00 ++ (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))) fragment0400698Acc00600 := object_fragment0400698_field_005 fuel (fragment0400698Field006Chars00 ++ (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))) fragment0400698Acc00700 := object_fragment0400698_field_006 fuel (fragment0400698Field007Chars00 ++ (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))) fragment0400698Acc00800 := object_fragment0400698_field_007 fuel (fragment0400698Field008Chars00 ++ (fragment0400698Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0400698Field009Chars00 ++ (tail))) fragment0400698Acc00900 := object_fragment0400698_field_008 fuel (fragment0400698Field009Chars00 ++ (tail))
    _ = .ok (fragment0400698Value, tail) := object_fragment0400698_field_009 fuel (tail)

noncomputable def fragment0402249Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0402249Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0402249Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '3'])
noncomputable def fragment0402249Acc00100 : List (String × SourceJson) := (fragment0402249Field000Key00, fragment0402249Field000Value00) :: fragment0402249Acc00000
noncomputable def fragment0402249Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '3', ',']

theorem object_fragment0402249_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0402249Field000Chars00 ++ tail)) fragment0402249Acc00000 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0402249Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_000"
  err.flush

noncomputable def fragment0402249Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0402249Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0402249Acc00200 : List (String × SourceJson) := (fragment0402249Field001Key00, fragment0402249Field001Value00) :: fragment0402249Acc00100
noncomputable def fragment0402249Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0402249_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0402249Field001Chars00 ++ tail)) fragment0402249Acc00100 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0402249Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_001"
  err.flush

noncomputable def fragment0402249Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0402249Field002Value00 : SourceJson := .str (String.ofList ['8', '0', '8', '1', '9', '4', '6', '8', '5', '6', '2', '8', '0', '1', '8', '4', '7', '1', '6', '5', '4', '1', '5', '2', '6', '3', '6', '0', '1', '7', '3', '4', '0', '8', '4', '4', '7', '8', '0', '5', '8', '1', '/', '8', '5', '8', '8', '5', '7', '4', '4', '2', '5', '2', '9', '4', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0402249Acc00300 : List (String × SourceJson) := (fragment0402249Field002Key00, fragment0402249Field002Value00) :: fragment0402249Acc00200
noncomputable def fragment0402249Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '0', '8', '1', '9', '4', '6', '8', '5', '6', '2', '8', '0', '1', '8', '4', '7', '1', '6', '5', '4', '1', '5', '2', '6', '3', '6', '0', '1', '7', '3', '4', '0', '8', '4', '4', '7', '8', '0', '5', '8', '1', '/', '8', '5', '8', '8', '5', '7', '4', '4', '2', '5', '2', '9', '4', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0402249_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0402249Field002Chars00 ++ tail)) fragment0402249Acc00200 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0402249Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_002"
  err.flush

noncomputable def fragment0402249Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0402249Field003Value00 : SourceJson := .str (String.ofList ['3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0'])
noncomputable def fragment0402249Acc00400 : List (String × SourceJson) := (fragment0402249Field003Key00, fragment0402249Field003Value00) :: fragment0402249Acc00300
noncomputable def fragment0402249Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0402249_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0402249Field003Chars00 ++ tail)) fragment0402249Acc00300 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0402249Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_003"
  err.flush

noncomputable def fragment0402249Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0402249Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['8', '0', '7', '/', '1', '7', '7', '9', '2'])]
noncomputable def fragment0402249Acc00500 : List (String × SourceJson) := (fragment0402249Field004Key00, fragment0402249Field004Value00) :: fragment0402249Acc00400
noncomputable def fragment0402249Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '/', '1', '7', '7', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0402249_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0402249Field004Chars00 ++ tail)) fragment0402249Acc00400 =
      SourceJson.object (fuel + 393) (SourceJson.white tail) fragment0402249Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_004"
  err.flush

noncomputable def fragment0402249Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0402249Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '1', '6', '8', '6', '9', '8', '5', '8', '5', '2', '9', '7', '3', '6', '9', '3', '0', '3', '7', '/', '2', '5', '6', '0', '8', '2', '3', '7', '5', '0', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '7', '5', '2', '5', '0', '4', '4', '2', '6', '1', '8', '1', '3', '6', '2', '5', '6', '3', '/', '3', '5', '8', '5', '1', '5', '3', '2', '5', '1', '1', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '7', '4', '5', '3', '1', '4', '4', '9', '9', '6', '3', '6', '3', '0', '1', '7', '9', '7', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '6', '9', '3', '3', '3', '9', '5', '5', '9', '5', '7', '8', '7', '0', '5', '0', '9', '1', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '6', '9', '6', '1', '5', '5', '4', '9', '7', '4', '8', '1', '8', '6', '7', '1', '8', '7', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '4', '8', '1', '3', '0', '5', '0', '3', '7', '7', '5', '9', '3', '6', '4', '2', '9', '7', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '8', '7', '9', '8', '3', '5', '0', '2', '6', '8', '2', '3', '0', '8', '9', '2', '3', '1', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '4', '3', '3', '7', '2', '3', '4', '5', '3', '3', '5', '7', '6', '6', '1', '8', '4', '7', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '0', '8', '6', '7', '0', '1', '6', '6', '8', '8', '3', '2', '5', '1', '8', '4', '5', '9', '/', '6', '4', '5', '3', '2', '7', '5', '8', '5', '2', '0', '8', '6', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '6', '4', '9', '0', '5', '5', '4', '8', '9', '9', '7', '8', '8', '5', '2', '8', '2', '4', '1', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0402249Acc00600 : List (String × SourceJson) := (fragment0402249Field005Key00, fragment0402249Field005Value00) :: fragment0402249Acc00500
noncomputable def fragment0402249Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '8', '6', '9', '8', '5', '8', '5', '2', '9', '7', '3', '6', '9', '3', '0', '3', '7', '/', '2', '5', '6', '0', '8', '2', '3', '7', '5', '0', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '5', '2', '5', '0', '4', '4', '2', '6', '1', '8', '1', '3', '6', '2', '5', '6', '3', '/', '3', '5', '8', '5', '1', '5', '3', '2', '5', '1', '1', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '7', '4', '5', '3', '1', '4', '4', '9', '9', '6', '3', '6', '3', '0', '1', '7', '9', '7', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '6', '9', '3', '3', '3', '9', '5', '5', '9', '5', '7', '8', '7', '0', '5', '0', '9', '1', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '6', '9', '6', '1', '5', '5', '4', '9', '7', '4', '8', '1', '8', '6', '7', '1', '8', '7', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '4', '8', '1', '3', '0', '5', '0', '3', '7', '7', '5', '9', '3', '6', '4', '2', '9', '7', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '8', '7', '9', '8', '3', '5', '0', '2', '6', '8', '2', '3', '0', '8', '9', '2', '3', '1', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '4', '3', '3', '7', '2', '3', '4', '5', '3', '3', '5', '7', '6', '6', '1', '8', '4', '7', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '0', '8', '6', '7', '0', '1', '6', '6', '8', '8', '3', '2', '5', '1', '8', '4', '5', '9', '/', '6', '4', '5', '3', '2', '7', '5', '8', '5', '2', '0', '8', '6', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '6', '4', '9', '0', '5', '5', '4', '8', '9', '9', '7', '8', '8', '5', '2', '8', '2', '4', '1', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0402249_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 393) (SourceJson.white (fragment0402249Field005Chars00 ++ tail)) fragment0402249Acc00500 =
      SourceJson.object (fuel + 392) (SourceJson.white tail) fragment0402249Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_005"
  err.flush

noncomputable def fragment0402249Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0402249Field006Value00 : SourceJson := .str (String.ofList ['2', '8', '2', '9', '3', '1', '5', '3', '0', '5', '8', '7', '7', '2', '3', '6', '5', '9', '2', '4', '1', '3', '7', '4', '5', '9', '3', '4', '3', '3', '7', '5', '9', '4', '2', '9', '9', '0', '8', '6', '1', '7', '0', '3', '1', '1', '7', '9', '3', '6', '7', '2', '/', '5', '0', '0', '6', '0', '6', '0', '1', '0', '8', '9', '0', '2', '0', '7', '2', '9', '2', '8', '5', '6', '9', '0', '3', '0', '4', '1', '6', '3', '2', '0', '0', '9', '6', '8', '3', '0', '4', '1', '4', '5', '2', '3', '1', '2', '9', '0', '0', '3', '9', '4', '5', '2', '1', '0', '1', '7', '4', '5', '6', '0', '5', '4', '6', '8', '7', '5'])
noncomputable def fragment0402249Acc00700 : List (String × SourceJson) := (fragment0402249Field006Key00, fragment0402249Field006Value00) :: fragment0402249Acc00600
noncomputable def fragment0402249Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '2', '9', '3', '1', '5', '3', '0', '5', '8', '7', '7', '2', '3', '6', '5', '9', '2', '4', '1', '3', '7', '4', '5', '9', '3', '4', '3', '3', '7', '5', '9', '4', '2', '9', '9', '0', '8', '6', '1', '7', '0', '3', '1', '1', '7', '9', '3', '6', '7', '2', '/', '5', '0', '0', '6', '0', '6', '0', '1', '0', '8', '9', '0', '2', '0', '7', '2', '9', '2', '8', '5', '6', '9', '0', '3', '0', '4', '1', '6', '3', '2', '0', '0', '9', '6', '8', '3', '0', '4', '1', '4', '5', '2', '3', '1', '2', '9', '0', '0', '3', '9', '4', '5', '2', '1', '0', '1', '7', '4', '5', '6', '0', '5', '4', '6', '8', '7', '5', '"', ',']

theorem object_fragment0402249_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 392) (SourceJson.white (fragment0402249Field006Chars00 ++ tail)) fragment0402249Acc00600 =
      SourceJson.object (fuel + 391) (SourceJson.white tail) fragment0402249Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_006"
  err.flush

noncomputable def fragment0402249Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0402249Field007Value00 : SourceJson := .str (String.ofList ['9', '3', '6', '2', '5', '0', '6', '8', '7', '4', '6', '5', '7', '0', '9', '0', '5', '9', '0', '8', '9', '6', '8', '9', '5', '7', '8', '3', '9', '3', '7', '6', '2', '0', '6', '8', '9', '8', '8', '5', '9', '6', '9', '6', '5', '9', '0', '0', '5', '9', '9', '1', '9', '3', '6', '3', '2', '3', '8', '8', '4', '3', '1', '7', '6', '0', '8', '5', '5', '2', '0', '2', '9', '2', '1', '5', '8', '8', '7', '1', '5', '1', '8', '2', '0', '1', '9', '5', '4', '7', '1', '9', '0', '7', '4', '2', '5', '5', '8', '2', '5', '8', '6', '1', '2', '4', '7', '8', '8', '3', '6', '3', '5', '6', '8', '4', '5', '2', '3', '5', '8', '2', '1', '4', '5', '3', '7', '7', '0', '7', '9', '3', '0', '7', '7', '2', '4', '1', '5', '4', '7', '9', '8', '8', '8', '0', '8', '5', '3', '2', '5', '7', '1', '5', '3', '9', '4', '0', '7', '1', '1', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '3', '2', '4', '3', '6', '9', '6', '0', '4', '3', '0', '4', '3', '0', '5', '2', '0', '6', '9', '4', '6', '9', '5', '1', '4', '5', '0', '9', '0', '3', '9', '5', '0', '2', '8', '8', '6', '7', '0', '6', '4', '3', '9', '5', '1', '5', '1', '2', '1', '0', '5', '7', '2', '4', '9', '2', '6', '2', '7', '4', '3', '0', '8', '6', '6', '4', '7', '2', '3', '3', '1', '1', '7', '7', '1', '1', '5', '2', '2', '1', '7', '4', '4', '4', '4', '3', '7', '8', '1', '3', '8', '5', '3', '7', '2', '3', '6', '1', '0', '1', '7', '2', '1', '4', '2', '8', '3', '1', '4', '6', '9', '6', '7', '3', '1', '5', '4', '2', '5', '8', '4', '4', '4', '7', '4', '1', '2', '5', '4', '8', '8', '9', '8', '4', '9', '0', '6', '5', '2', '9', '2', '8', '1', '5', '6', '4', '3', '3', '6', '9', '6', '9', '6', '2', '1', '2', '3', '5', '5', '5', '5', '0', '6', '3', '8', '8', '4', '9', '5', '3', '3', '5', '9', '6', '6', '4', '8', '6', '6', '1', '5', '3', '9', '9', '7', '7', '9', '8', '7', '4', '5', '6', '9', '3', '4', '5', '2', '6', '9'])
noncomputable def fragment0402249Acc00800 : List (String × SourceJson) := (fragment0402249Field007Key00, fragment0402249Field007Value00) :: fragment0402249Acc00700
noncomputable def fragment0402249Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '3', '6', '2', '5', '0', '6', '8', '7', '4', '6', '5', '7', '0', '9', '0', '5', '9', '0', '8', '9', '6', '8', '9', '5', '7', '8', '3', '9', '3', '7', '6', '2', '0', '6', '8', '9', '8', '8', '5', '9', '6', '9', '6', '5', '9', '0', '0', '5', '9', '9', '1', '9', '3', '6', '3', '2', '3', '8', '8', '4', '3', '1', '7', '6', '0', '8', '5', '5', '2', '0', '2', '9', '2', '1', '5', '8', '8', '7', '1', '5', '1', '8', '2', '0', '1', '9', '5', '4', '7', '1', '9', '0', '7', '4', '2', '5', '5', '8', '2', '5', '8', '6', '1', '2', '4', '7', '8', '8', '3', '6', '3', '5', '6', '8', '4', '5', '2', '3', '5', '8', '2', '1', '4', '5', '3', '7', '7', '0', '7', '9', '3', '0', '7', '7', '2', '4', '1', '5', '4', '7', '9', '8', '8', '8', '0', '8', '5', '3', '2', '5', '7', '1', '5', '3', '9', '4', '0', '7', '1', '1', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '3', '2', '4', '3', '6', '9', '6', '0', '4', '3', '0', '4', '3', '0', '5', '2', '0', '6', '9', '4', '6', '9', '5', '1', '4', '5', '0', '9', '0', '3', '9', '5', '0', '2', '8', '8', '6', '7', '0', '6', '4', '3', '9', '5', '1', '5', '1', '2', '1', '0', '5', '7', '2', '4', '9', '2', '6', '2', '7', '4', '3', '0', '8', '6', '6', '4', '7', '2', '3', '3', '1', '1', '7', '7', '1', '1', '5', '2', '2', '1', '7', '4', '4', '4', '4', '3', '7', '8', '1', '3', '8', '5', '3', '7', '2', '3', '6', '1', '0', '1', '7', '2', '1', '4', '2', '8', '3', '1', '4', '6', '9', '6', '7', '3', '1', '5', '4', '2', '5', '8', '4', '4', '4', '7', '4', '1', '2', '5', '4', '8', '8', '9', '8', '4', '9', '0', '6', '5', '2', '9', '2', '8', '1', '5', '6', '4', '3', '3', '6', '9', '6', '9', '6', '2', '1', '2', '3', '5', '5', '5', '5', '0', '6', '3', '8', '8', '4', '9', '5', '3', '3', '5', '9', '6', '6', '4', '8', '6', '6', '1', '5', '3', '9', '9', '7', '7', '9', '8', '7', '4', '5', '6', '9', '3', '4', '5', '2', '6', '9', '"', ',']

theorem object_fragment0402249_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 391) (SourceJson.white (fragment0402249Field007Chars00 ++ tail)) fragment0402249Acc00700 =
      SourceJson.object (fuel + 390) (SourceJson.white tail) fragment0402249Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_007"
  err.flush

noncomputable def fragment0402249Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0402249Field008Value00 : SourceJson := .str (String.ofList ['4', '4', '7', '7', '8', '0', '1', '8', '6', '3', '7', '7', '5', '4'])
noncomputable def fragment0402249Acc00900 : List (String × SourceJson) := (fragment0402249Field008Key00, fragment0402249Field008Value00) :: fragment0402249Acc00800
noncomputable def fragment0402249Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '7', '7', '8', '0', '1', '8', '6', '3', '7', '7', '5', '4', '"', ',']

theorem object_fragment0402249_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 390) (SourceJson.white (fragment0402249Field008Chars00 ++ tail)) fragment0402249Acc00800 =
      SourceJson.object (fuel + 389) (SourceJson.white tail) fragment0402249Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_008"
  err.flush

noncomputable def fragment0402249Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0402249Field009Value00 : SourceJson := .str (String.ofList ['3', '1', '8', '0', '2', '5', '4', '0', '8', '0', '9', '9', '0', '7', '3'])
noncomputable def fragment0402249Acc01000 : List (String × SourceJson) := (fragment0402249Field009Key00, fragment0402249Field009Value00) :: fragment0402249Acc00900
noncomputable def fragment0402249Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '8', '0', '2', '5', '4', '0', '8', '0', '9', '9', '0', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0402249_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 389) (SourceJson.white (fragment0402249Field009Chars00 ++ tail)) fragment0402249Acc00900 =
      .ok (.obj (fragment0402249Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0402249_object_field_009"
  err.flush

noncomputable def fragment0402249Chars : List Char := '{' :: (fragment0402249Field000Chars00 ++ fragment0402249Field001Chars00 ++ fragment0402249Field002Chars00 ++ fragment0402249Field003Chars00 ++ fragment0402249Field004Chars00 ++ fragment0402249Field005Chars00 ++ fragment0402249Field006Chars00 ++ fragment0402249Field007Chars00 ++ fragment0402249Field008Chars00 ++ fragment0402249Field009Chars00)
noncomputable def fragment0402249Value : SourceJson := .obj (fragment0402249Acc01000.reverse)

theorem value_fragment0402249 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 399) (fragment0402249Chars ++ tail) =
      .ok (fragment0402249Value, tail) := by
  have hinput : fragment0402249Chars ++ tail = '{' :: (fragment0402249Field000Chars00 ++ (fragment0402249Field001Chars00 ++ (fragment0402249Field002Chars00 ++ (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0402249Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 399) (fragment0402249Chars ++ tail) =
        SourceJson.value (fuel + 399) ('{' :: (fragment0402249Field000Chars00 ++ (fragment0402249Field001Chars00 ++ (fragment0402249Field002Chars00 ++ (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 399)) hinput
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0402249Field000Chars00 ++ (fragment0402249Field001Chars00 ++ (fragment0402249Field002Chars00 ++ (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))))))))) fragment0402249Acc00000 := by rfl
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0402249Field001Chars00 ++ (fragment0402249Field002Chars00 ++ (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))))))))) fragment0402249Acc00100 := object_fragment0402249_field_000 fuel (fragment0402249Field001Chars00 ++ (fragment0402249Field002Chars00 ++ (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0402249Field002Chars00 ++ (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))))))) fragment0402249Acc00200 := object_fragment0402249_field_001 fuel (fragment0402249Field002Chars00 ++ (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))))))) fragment0402249Acc00300 := object_fragment0402249_field_002 fuel (fragment0402249Field003Chars00 ++ (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))))) fragment0402249Acc00400 := object_fragment0402249_field_003 fuel (fragment0402249Field004Chars00 ++ (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 393) (SourceJson.white (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))))) fragment0402249Acc00500 := object_fragment0402249_field_004 fuel (fragment0402249Field005Chars00 ++ (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 392) (SourceJson.white (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))) fragment0402249Acc00600 := object_fragment0402249_field_005 fuel (fragment0402249Field006Chars00 ++ (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 391) (SourceJson.white (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))) fragment0402249Acc00700 := object_fragment0402249_field_006 fuel (fragment0402249Field007Chars00 ++ (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 390) (SourceJson.white (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))) fragment0402249Acc00800 := object_fragment0402249_field_007 fuel (fragment0402249Field008Chars00 ++ (fragment0402249Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 389) (SourceJson.white (fragment0402249Field009Chars00 ++ (tail))) fragment0402249Acc00900 := object_fragment0402249_field_008 fuel (fragment0402249Field009Chars00 ++ (tail))
    _ = .ok (fragment0402249Value, tail) := object_fragment0402249_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0102_before_reader"
  err.flush

noncomputable def chunk0102LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0102SuffixChars00 : List Char := [',']
noncomputable def chunk0102Chars00 : List Char := chunk0102LeadChars00 ++ fragment0400698Chars ++ chunk0102SuffixChars00
noncomputable def chunk0102Push00 (acc : List SourceJson) : List SourceJson := fragment0400698Value :: acc

noncomputable def chunk0102AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0102_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 502)
      (SourceJson.white (chunk0102LeadChars00 ++ (fragment0400698Chars ++ rest))) acc =
      (SourceJson.value (fuel + 501) (fragment0400698Chars ++ rest)).bind
        (chunk0102AfterValue00 (fuel + 501) acc) := by rfl

theorem array_chunk0102 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 502) (SourceJson.white (chunk0102Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 501) (SourceJson.white tail) (chunk0102Push00 acc) := by
  have hinput : chunk0102Chars00 ++ tail = chunk0102LeadChars00 ++ (fragment0400698Chars ++ (chunk0102SuffixChars00 ++ tail)) := by
    simp only [chunk0102Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 502) (SourceJson.white (chunk0102Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 502)
          (SourceJson.white (chunk0102LeadChars00 ++ (fragment0400698Chars ++ (chunk0102SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 502) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 501) (fragment0400698Chars ++ (chunk0102SuffixChars00 ++ tail))).bind
        (chunk0102AfterValue00 (fuel + 501) acc) := array_chunk0102_head fuel (chunk0102SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0400698Value, chunk0102SuffixChars00 ++ tail)).bind
        (chunk0102AfterValue00 (fuel + 501) acc) :=
      congrArg (fun result => result.bind (chunk0102AfterValue00 (fuel + 501) acc))
        (value_fragment0400698 (fuel + 296) (chunk0102SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 501) (SourceJson.white tail) (chunk0102Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0102_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0103_before_reader"
  err.flush

noncomputable def chunk0103LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0103SuffixChars00 : List Char := [',']
noncomputable def chunk0103Chars00 : List Char := chunk0103LeadChars00 ++ fragment0402249Chars ++ chunk0103SuffixChars00
noncomputable def chunk0103Push00 (acc : List SourceJson) : List SourceJson := fragment0402249Value :: acc

noncomputable def chunk0103AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0103_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 501)
      (SourceJson.white (chunk0103LeadChars00 ++ (fragment0402249Chars ++ rest))) acc =
      (SourceJson.value (fuel + 500) (fragment0402249Chars ++ rest)).bind
        (chunk0103AfterValue00 (fuel + 500) acc) := by rfl

theorem array_chunk0103 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 501) (SourceJson.white (chunk0103Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 500) (SourceJson.white tail) (chunk0103Push00 acc) := by
  have hinput : chunk0103Chars00 ++ tail = chunk0103LeadChars00 ++ (fragment0402249Chars ++ (chunk0103SuffixChars00 ++ tail)) := by
    simp only [chunk0103Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 501) (SourceJson.white (chunk0103Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 501)
          (SourceJson.white (chunk0103LeadChars00 ++ (fragment0402249Chars ++ (chunk0103SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 501) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 500) (fragment0402249Chars ++ (chunk0103SuffixChars00 ++ tail))).bind
        (chunk0103AfterValue00 (fuel + 500) acc) := array_chunk0103_head fuel (chunk0103SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0402249Value, chunk0103SuffixChars00 ++ tail)).bind
        (chunk0103AfterValue00 (fuel + 500) acc) :=
      congrArg (fun result => result.bind (chunk0103AfterValue00 (fuel + 500) acc))
        (value_fragment0402249 (fuel + 101) (chunk0103SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 500) (SourceJson.white tail) (chunk0103Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0103_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0102Chars00 ++ chunk0103Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0103Push00 (chunk0102Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 502) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 500) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 502) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 502) (SourceJson.white (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 502) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 501) (SourceJson.white (chunk0103Chars00 ++ (tail))) (chunk0102Push00 (acc)) := array_chunk0102 fuel (chunk0103Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 500) (SourceJson.white tail) (blockPush acc) := array_chunk0103 fuel (tail) (chunk0102Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 400692).take 3478 = blockChars := by rfl

theorem block_original_split : sourceRest 400692 = blockChars ++ sourceRest 404170 := by
  calc
    sourceRest 400692 = (sourceRest 400692).take 3478 ++ (sourceRest 400692).drop 3478 :=
      (List.take_append_drop 3478 (sourceRest 400692)).symm
    _ = blockChars ++ (sourceRest 400692).drop 3478 :=
      congrArg (fun part => part ++ (sourceRest 400692).drop 3478) block_original_prefix
    _ = blockChars ++ sourceRest 404170 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 400692 3478)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 502) (SourceJson.white (sourceRest 400692)) acc =
      SourceJson.array (fuel + 500) (SourceJson.white (sourceRest 404170)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 502) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 404170) acc)

#print axioms object_fragment0400698_field_000
#print axioms object_fragment0400698_field_001
#print axioms object_fragment0400698_field_002
#print axioms object_fragment0400698_field_003
#print axioms object_fragment0400698_field_004
#print axioms object_fragment0400698_field_005
#print axioms object_fragment0400698_field_006
#print axioms object_fragment0400698_field_007
#print axioms object_fragment0400698_field_008
#print axioms object_fragment0400698_field_009
#print axioms value_fragment0400698
#print axioms object_fragment0402249_field_000
#print axioms object_fragment0402249_field_001
#print axioms object_fragment0402249_field_002
#print axioms object_fragment0402249_field_003
#print axioms object_fragment0402249_field_004
#print axioms object_fragment0402249_field_005
#print axioms object_fragment0402249_field_006
#print axioms object_fragment0402249_field_007
#print axioms object_fragment0402249_field_008
#print axioms object_fragment0402249_field_009
#print axioms value_fragment0402249
#print axioms array_chunk0102_head
#print axioms array_chunk0102
#print axioms array_chunk0103_head
#print axioms array_chunk0103
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock052

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
