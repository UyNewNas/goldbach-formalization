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

namespace SimplicesBlock014

noncomputable def fragment0273150Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0273150Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0273150Field000Value00 : SourceJson := .number (String.ofList ['2', '8'])
noncomputable def fragment0273150Acc00100 : List (String × SourceJson) := (fragment0273150Field000Key00, fragment0273150Field000Value00) :: fragment0273150Acc00000
noncomputable def fragment0273150Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '8', ',']

theorem object_fragment0273150_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0273150Field000Chars00 ++ tail)) fragment0273150Acc00000 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0273150Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_000"
  err.flush

noncomputable def fragment0273150Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0273150Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0273150Acc00200 : List (String × SourceJson) := (fragment0273150Field001Key00, fragment0273150Field001Value00) :: fragment0273150Acc00100
noncomputable def fragment0273150Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0273150_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0273150Field001Chars00 ++ tail)) fragment0273150Acc00100 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0273150Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_001"
  err.flush

noncomputable def fragment0273150Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0273150Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '4', '3', '7', '6', '0', '4', '4', '1', '6', '4', '0', '8', '1', '8', '1', '3', '5', '9', '4', '9', '0', '1', '9', '3', '2', '2', '7', '5', '9', '8', '7', '3', '2', '5', '5', '2', '1', '/', '5', '9', '4', '7', '9', '0', '3', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0273150Acc00300 : List (String × SourceJson) := (fragment0273150Field002Key00, fragment0273150Field002Value00) :: fragment0273150Acc00200
noncomputable def fragment0273150Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '4', '3', '7', '6', '0', '4', '4', '1', '6', '4', '0', '8', '1', '8', '1', '3', '5', '9', '4', '9', '0', '1', '9', '3', '2', '2', '7', '5', '9', '8', '7', '3', '2', '5', '5', '2', '1', '/', '5', '9', '4', '7', '9', '0', '3', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0273150_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0273150Field002Chars00 ++ tail)) fragment0273150Acc00200 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0273150Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_002"
  err.flush

noncomputable def fragment0273150Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0273150Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0273150Acc00400 : List (String × SourceJson) := (fragment0273150Field003Key00, fragment0273150Field003Value00) :: fragment0273150Acc00300
noncomputable def fragment0273150Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0273150_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0273150Field003Chars00 ++ tail)) fragment0273150Acc00300 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0273150Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_003"
  err.flush

noncomputable def fragment0273150Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0273150Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0273150Acc00500 : List (String × SourceJson) := (fragment0273150Field004Key00, fragment0273150Field004Value00) :: fragment0273150Acc00400
noncomputable def fragment0273150Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0273150_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0273150Field004Chars00 ++ tail)) fragment0273150Acc00400 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0273150Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_004"
  err.flush

noncomputable def fragment0273150Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0273150Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '7', '8', '7', '2', '2', '9', '7', '6', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '7', '5', '8', '0', '6', '4', '1', '8', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '9', '1', '9', '5', '4', '1', '6', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '0', '8', '6', '0', '3', '5', '6', '9', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '8', '7', '3', '5', '1', '0', '1', '2', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '4', '3', '5', '7', '7', '4', '0', '3', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '5', '6', '9', '3', '3', '5', '8', '7', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '3', '8', '5', '9', '0', '4', '2', '6', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '3', '8', '5', '8', '5', '7', '2', '2', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '1', '9', '6', '5', '2', '2', '3', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0273150Acc00600 : List (String × SourceJson) := (fragment0273150Field005Key00, fragment0273150Field005Value00) :: fragment0273150Acc00500
noncomputable def fragment0273150Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '7', '2', '2', '9', '7', '6', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '5', '8', '0', '6', '4', '1', '8', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '9', '1', '9', '5', '4', '1', '6', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '0', '8', '6', '0', '3', '5', '6', '9', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '8', '7', '3', '5', '1', '0', '1', '2', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '4', '3', '5', '7', '7', '4', '0', '3', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '5', '6', '9', '3', '3', '5', '8', '7', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '8', '5', '9', '0', '4', '2', '6', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '8', '5', '8', '5', '7', '2', '2', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '1', '9', '6', '5', '2', '2', '3', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0273150_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0273150Field005Chars00 ++ tail)) fragment0273150Acc00500 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0273150Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_005"
  err.flush

noncomputable def fragment0273150Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0273150Field006Value00 : SourceJson := .str (String.ofList ['6', '0', '2', '8', '8', '7', '9', '8', '2', '9', '2', '5', '9', '3', '6', '8', '7', '5', '8', '2', '4', '9', '6', '6', '6', '8', '0', '6', '0', '1', '4', '9', '6', '2', '4', '8', '4', '9', '1', '3', '2', '3', '3', '1', '3', '3', '0', '0', '0', '0', '/', '4', '0', '6', '9', '6', '3', '6', '0', '7', '9', '4', '8', '7', '6', '8', '9', '4', '3', '2', '3', '2', '0', '8', '9', '2', '7', '9', '8', '1', '6', '6', '0', '6', '1', '6', '3', '4', '8', '3', '9', '9', '3', '2', '6', '6', '9', '4', '7', '0', '5', '7', '4', '0', '9', '9', '3', '2', '1', '5', '9', '4', '5', '9', '8', '7'])
noncomputable def fragment0273150Acc00700 : List (String × SourceJson) := (fragment0273150Field006Key00, fragment0273150Field006Value00) :: fragment0273150Acc00600
noncomputable def fragment0273150Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '0', '2', '8', '8', '7', '9', '8', '2', '9', '2', '5', '9', '3', '6', '8', '7', '5', '8', '2', '4', '9', '6', '6', '6', '8', '0', '6', '0', '1', '4', '9', '6', '2', '4', '8', '4', '9', '1', '3', '2', '3', '3', '1', '3', '3', '0', '0', '0', '0', '/', '4', '0', '6', '9', '6', '3', '6', '0', '7', '9', '4', '8', '7', '6', '8', '9', '4', '3', '2', '3', '2', '0', '8', '9', '2', '7', '9', '8', '1', '6', '6', '0', '6', '1', '6', '3', '4', '8', '3', '9', '9', '3', '2', '6', '6', '9', '4', '7', '0', '5', '7', '4', '0', '9', '9', '3', '2', '1', '5', '9', '4', '5', '9', '8', '7', '"', ',']

theorem object_fragment0273150_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0273150Field006Chars00 ++ tail)) fragment0273150Acc00600 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0273150Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_006"
  err.flush

noncomputable def fragment0273150Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0273150Field007Value00 : SourceJson := .str (String.ofList ['6', '8', '8', '9', '1', '2', '8', '8', '0', '2', '7', '7', '0', '0', '1', '8', '7', '6', '2', '5', '5', '6', '4', '9', '5', '5', '5', '1', '5', '7', '0', '0', '1', '3', '0', '3', '1', '6', '3', '5', '9', '2', '4', '6', '9', '9', '1', '9', '8', '9', '3', '2', '5', '1', '5', '4', '6', '9', '9', '7', '6', '9', '2', '8', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '3', '3', '5', '5', '8', '4', '6', '7', '9', '5', '1', '1', '2', '9', '1', '3', '5', '4', '0', '6', '1', '8', '0', '3', '1', '7', '8', '8', '6', '7', '9', '2', '5', '3', '2', '1', '3', '6', '3', '6', '7', '2', '2', '9', '4', '8', '8', '1', '5', '1', '5', '0', '7', '3', '4', '4', '9', '6', '8', '3', '1', '2', '3', '2', '0', '6', '5', '3', '8', '2', '6', '0', '4', '9', '1', '3', '6', '2', '5', '4', '6', '5', '4', '0', '6', '4', '7', '1', '4', '4', '4', '3', '8', '9', '5', '5', '8', '0', '8', '8', '8', '9'])
noncomputable def fragment0273150Acc00800 : List (String × SourceJson) := (fragment0273150Field007Key00, fragment0273150Field007Value00) :: fragment0273150Acc00700
noncomputable def fragment0273150Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '8', '8', '9', '1', '2', '8', '8', '0', '2', '7', '7', '0', '0', '1', '8', '7', '6', '2', '5', '5', '6', '4', '9', '5', '5', '5', '1', '5', '7', '0', '0', '1', '3', '0', '3', '1', '6', '3', '5', '9', '2', '4', '6', '9', '9', '1', '9', '8', '9', '3', '2', '5', '1', '5', '4', '6', '9', '9', '7', '6', '9', '2', '8', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '3', '3', '5', '5', '8', '4', '6', '7', '9', '5', '1', '1', '2', '9', '1', '3', '5', '4', '0', '6', '1', '8', '0', '3', '1', '7', '8', '8', '6', '7', '9', '2', '5', '3', '2', '1', '3', '6', '3', '6', '7', '2', '2', '9', '4', '8', '8', '1', '5', '1', '5', '0', '7', '3', '4', '4', '9', '6', '8', '3', '1', '2', '3', '2', '0', '6', '5', '3', '8', '2', '6', '0', '4', '9', '1', '3', '6', '2', '5', '4', '6', '5', '4', '0', '6', '4', '7', '1', '4', '4', '4', '3', '8', '9', '5', '5', '8', '0', '8', '8', '8', '9', '"', ',']

theorem object_fragment0273150_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0273150Field007Chars00 ++ tail)) fragment0273150Acc00700 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0273150Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_007"
  err.flush

noncomputable def fragment0273150Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0273150Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '3', '7', '0', '9', '5', '4', '4', '4', '4', '5', '7', '0'])
noncomputable def fragment0273150Acc00900 : List (String × SourceJson) := (fragment0273150Field008Key00, fragment0273150Field008Value00) :: fragment0273150Acc00800
noncomputable def fragment0273150Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '3', '7', '0', '9', '5', '4', '4', '4', '4', '5', '7', '0', '"', ',']

theorem object_fragment0273150_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0273150Field008Chars00 ++ tail)) fragment0273150Acc00800 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0273150Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_008"
  err.flush

noncomputable def fragment0273150Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0273150Field009Value00 : SourceJson := .str (String.ofList ['8', '6', '1', '5', '0', '3', '7', '8', '2', '1', '7', '2', '8', '9', '4'])
noncomputable def fragment0273150Acc01000 : List (String × SourceJson) := (fragment0273150Field009Key00, fragment0273150Field009Value00) :: fragment0273150Acc00900
noncomputable def fragment0273150Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '1', '5', '0', '3', '7', '8', '2', '1', '7', '2', '8', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0273150_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0273150Field009Chars00 ++ tail)) fragment0273150Acc00900 =
      .ok (.obj (fragment0273150Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0273150_object_field_009"
  err.flush

noncomputable def fragment0273150Chars : List Char := '{' :: (fragment0273150Field000Chars00 ++ fragment0273150Field001Chars00 ++ fragment0273150Field002Chars00 ++ fragment0273150Field003Chars00 ++ fragment0273150Field004Chars00 ++ fragment0273150Field005Chars00 ++ fragment0273150Field006Chars00 ++ fragment0273150Field007Chars00 ++ fragment0273150Field008Chars00 ++ fragment0273150Field009Chars00)
noncomputable def fragment0273150Value : SourceJson := .obj (fragment0273150Acc01000.reverse)

theorem value_fragment0273150 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 204) (fragment0273150Chars ++ tail) =
      .ok (fragment0273150Value, tail) := by
  have hinput : fragment0273150Chars ++ tail = '{' :: (fragment0273150Field000Chars00 ++ (fragment0273150Field001Chars00 ++ (fragment0273150Field002Chars00 ++ (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0273150Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 204) (fragment0273150Chars ++ tail) =
        SourceJson.value (fuel + 204) ('{' :: (fragment0273150Field000Chars00 ++ (fragment0273150Field001Chars00 ++ (fragment0273150Field002Chars00 ++ (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 204)) hinput
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0273150Field000Chars00 ++ (fragment0273150Field001Chars00 ++ (fragment0273150Field002Chars00 ++ (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))))))))) fragment0273150Acc00000 := by rfl
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0273150Field001Chars00 ++ (fragment0273150Field002Chars00 ++ (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))))))))) fragment0273150Acc00100 := object_fragment0273150_field_000 fuel (fragment0273150Field001Chars00 ++ (fragment0273150Field002Chars00 ++ (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0273150Field002Chars00 ++ (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))))))) fragment0273150Acc00200 := object_fragment0273150_field_001 fuel (fragment0273150Field002Chars00 ++ (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))))))) fragment0273150Acc00300 := object_fragment0273150_field_002 fuel (fragment0273150Field003Chars00 ++ (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))))) fragment0273150Acc00400 := object_fragment0273150_field_003 fuel (fragment0273150Field004Chars00 ++ (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))))) fragment0273150Acc00500 := object_fragment0273150_field_004 fuel (fragment0273150Field005Chars00 ++ (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))) fragment0273150Acc00600 := object_fragment0273150_field_005 fuel (fragment0273150Field006Chars00 ++ (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))) fragment0273150Acc00700 := object_fragment0273150_field_006 fuel (fragment0273150Field007Chars00 ++ (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))) fragment0273150Acc00800 := object_fragment0273150_field_007 fuel (fragment0273150Field008Chars00 ++ (fragment0273150Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0273150Field009Chars00 ++ (tail))) fragment0273150Acc00900 := object_fragment0273150_field_008 fuel (fragment0273150Field009Chars00 ++ (tail))
    _ = .ok (fragment0273150Value, tail) := object_fragment0273150_field_009 fuel (tail)

noncomputable def fragment0274681Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0274681Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0274681Field000Value00 : SourceJson := .number (String.ofList ['2', '9'])
noncomputable def fragment0274681Acc00100 : List (String × SourceJson) := (fragment0274681Field000Key00, fragment0274681Field000Value00) :: fragment0274681Acc00000
noncomputable def fragment0274681Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '9', ',']

theorem object_fragment0274681_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0274681Field000Chars00 ++ tail)) fragment0274681Acc00000 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0274681Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_000"
  err.flush

noncomputable def fragment0274681Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0274681Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0274681Acc00200 : List (String × SourceJson) := (fragment0274681Field001Key00, fragment0274681Field001Value00) :: fragment0274681Acc00100
noncomputable def fragment0274681Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0274681_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0274681Field001Chars00 ++ tail)) fragment0274681Acc00100 =
      SourceJson.object (fuel + 191) (SourceJson.white tail) fragment0274681Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_001"
  err.flush

noncomputable def fragment0274681Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0274681Field002Value00 : SourceJson := .str (String.ofList ['7', '0', '6', '9', '7', '5', '7', '5', '3', '8', '7', '8', '1', '9', '7', '9', '3', '3', '1', '5', '2', '5', '2', '1', '4', '7', '0', '8', '8', '6', '2', '3', '0', '8', '1', '1', '5', '6', '2', '9', '9', '/', '2', '2', '4', '8', '3', '0', '7', '4', '0', '2', '3', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0274681Acc00300 : List (String × SourceJson) := (fragment0274681Field002Key00, fragment0274681Field002Value00) :: fragment0274681Acc00200
noncomputable def fragment0274681Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '0', '6', '9', '7', '5', '7', '5', '3', '8', '7', '8', '1', '9', '7', '9', '3', '3', '1', '5', '2', '5', '2', '1', '4', '7', '0', '8', '8', '6', '2', '3', '0', '8', '1', '1', '5', '6', '2', '9', '9', '/', '2', '2', '4', '8', '3', '0', '7', '4', '0', '2', '3', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0274681_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0274681Field002Chars00 ++ tail)) fragment0274681Acc00200 =
      SourceJson.object (fuel + 190) (SourceJson.white tail) fragment0274681Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_002"
  err.flush

noncomputable def fragment0274681Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0274681Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0274681Acc00400 : List (String × SourceJson) := (fragment0274681Field003Key00, fragment0274681Field003Value00) :: fragment0274681Acc00300
noncomputable def fragment0274681Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0274681_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 190) (SourceJson.white (fragment0274681Field003Chars00 ++ tail)) fragment0274681Acc00300 =
      SourceJson.object (fuel + 189) (SourceJson.white tail) fragment0274681Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_003"
  err.flush

noncomputable def fragment0274681Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0274681Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0274681Acc00500 : List (String × SourceJson) := (fragment0274681Field004Key00, fragment0274681Field004Value00) :: fragment0274681Acc00400
noncomputable def fragment0274681Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0274681_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 189) (SourceJson.white (fragment0274681Field004Chars00 ++ tail)) fragment0274681Acc00400 =
      SourceJson.object (fuel + 188) (SourceJson.white tail) fragment0274681Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_004"
  err.flush

noncomputable def fragment0274681Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0274681Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '4', '8', '7', '8', '2', '2', '6', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '1', '8', '8', '9', '3', '1', '6', '8', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '5', '5', '3', '6', '8', '4', '7', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '2', '2', '7', '2', '0', '7', '6', '5', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '6', '5', '1', '9', '1', '2', '8', '3', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '6', '3', '9', '5', '2', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '9', '4', '0', '9', '8', '1', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '1', '0', '2', '4', '7', '6', '1', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '8', '3', '0', '5', '8', '6', '0', '3', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '5', '0', '5', '1', '9', '7', '3', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0274681Acc00600 : List (String × SourceJson) := (fragment0274681Field005Key00, fragment0274681Field005Value00) :: fragment0274681Acc00500
noncomputable def fragment0274681Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '4', '8', '7', '8', '2', '2', '6', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '8', '8', '9', '3', '1', '6', '8', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '5', '3', '6', '8', '4', '7', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '2', '2', '7', '2', '0', '7', '6', '5', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '6', '5', '1', '9', '1', '2', '8', '3', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '6', '3', '9', '5', '2', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '9', '4', '0', '9', '8', '1', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '1', '0', '2', '4', '7', '6', '1', '/', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '8', '3', '0', '5', '8', '6', '0', '3', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '5', '0', '5', '1', '9', '7', '3', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0274681_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 188) (SourceJson.white (fragment0274681Field005Chars00 ++ tail)) fragment0274681Acc00500 =
      SourceJson.object (fuel + 187) (SourceJson.white tail) fragment0274681Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_005"
  err.flush

noncomputable def fragment0274681Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0274681Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '6', '6', '7', '5', '9', '9', '9', '2', '4', '6', '5', '3', '3', '3', '8', '0', '6', '5', '1', '9', '6', '9', '5', '6', '9', '2', '9', '3', '8', '9', '6', '7', '1', '0', '8', '6', '6', '5', '6', '3', '5', '9', '6', '3', '7', '6', '2', '5', '0', '/', '8', '2', '6', '5', '0', '2', '5', '5', '7', '4', '1', '2', '7', '8', '6', '0', '5', '0', '0', '2', '8', '8', '4', '8', '1', '8', '0', '2', '4', '5', '1', '1', '3', '6', '5', '6', '6', '5', '9', '2', '9', '4', '0', '3', '9', '5', '1', '6', '0', '0', '2', '3', '1', '4', '4', '9', '3', '5', '6', '0', '1', '8', '5', '4', '3'])
noncomputable def fragment0274681Acc00700 : List (String × SourceJson) := (fragment0274681Field006Key00, fragment0274681Field006Value00) :: fragment0274681Acc00600
noncomputable def fragment0274681Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '6', '6', '7', '5', '9', '9', '9', '2', '4', '6', '5', '3', '3', '3', '8', '0', '6', '5', '1', '9', '6', '9', '5', '6', '9', '2', '9', '3', '8', '9', '6', '7', '1', '0', '8', '6', '6', '5', '6', '3', '5', '9', '6', '3', '7', '6', '2', '5', '0', '/', '8', '2', '6', '5', '0', '2', '5', '5', '7', '4', '1', '2', '7', '8', '6', '0', '5', '0', '0', '2', '8', '8', '4', '8', '1', '8', '0', '2', '4', '5', '1', '1', '3', '6', '5', '6', '6', '5', '9', '2', '9', '4', '0', '3', '9', '5', '1', '6', '0', '0', '2', '3', '1', '4', '4', '9', '3', '5', '6', '0', '1', '8', '5', '4', '3', '"', ',']

theorem object_fragment0274681_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 187) (SourceJson.white (fragment0274681Field006Chars00 ++ tail)) fragment0274681Acc00600 =
      SourceJson.object (fuel + 186) (SourceJson.white tail) fragment0274681Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_006"
  err.flush

noncomputable def fragment0274681Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0274681Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '2', '2', '7', '2', '9', '8', '4', '9', '9', '3', '9', '4', '7', '4', '7', '6', '3', '9', '6', '0', '2', '2', '5', '2', '1', '2', '0', '7', '9', '6', '0', '2', '8', '3', '0', '6', '5', '0', '2', '8', '4', '2', '3', '7', '4', '7', '7', '3', '9', '5', '6', '4', '3', '4', '8', '8', '0', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '4', '1', '5', '3', '4', '6', '1', '1', '5', '2', '0', '1', '2', '6', '0', '6', '5', '5', '0', '6', '7', '6', '1', '8', '9', '6', '9', '3', '8', '1', '1', '9', '0', '0', '6', '7', '8', '6', '9', '3', '7', '2', '8', '8', '7', '2', '1', '9', '5', '0', '8', '1', '3', '1', '1', '2', '0', '8', '9', '4', '7', '2', '6', '2', '3', '0', '5', '1', '7', '1', '5', '5', '9', '8', '8', '8', '5', '0', '0', '5', '8', '4', '0', '2', '1', '7', '0', '7', '6', '4', '2', '2', '2', '7', '8', '7'])
noncomputable def fragment0274681Acc00800 : List (String × SourceJson) := (fragment0274681Field007Key00, fragment0274681Field007Value00) :: fragment0274681Acc00700
noncomputable def fragment0274681Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '2', '2', '7', '2', '9', '8', '4', '9', '9', '3', '9', '4', '7', '4', '7', '6', '3', '9', '6', '0', '2', '2', '5', '2', '1', '2', '0', '7', '9', '6', '0', '2', '8', '3', '0', '6', '5', '0', '2', '8', '4', '2', '3', '7', '4', '7', '7', '3', '9', '5', '6', '4', '3', '4', '8', '8', '0', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '4', '1', '5', '3', '4', '6', '1', '1', '5', '2', '0', '1', '2', '6', '0', '6', '5', '5', '0', '6', '7', '6', '1', '8', '9', '6', '9', '3', '8', '1', '1', '9', '0', '0', '6', '7', '8', '6', '9', '3', '7', '2', '8', '8', '7', '2', '1', '9', '5', '0', '8', '1', '3', '1', '1', '2', '0', '8', '9', '4', '7', '2', '6', '2', '3', '0', '5', '1', '7', '1', '5', '5', '9', '8', '8', '8', '5', '0', '0', '5', '8', '4', '0', '2', '1', '7', '0', '7', '6', '4', '2', '2', '2', '7', '8', '7', '"', ',']

theorem object_fragment0274681_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 186) (SourceJson.white (fragment0274681Field007Chars00 ++ tail)) fragment0274681Acc00700 =
      SourceJson.object (fuel + 185) (SourceJson.white tail) fragment0274681Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_007"
  err.flush

noncomputable def fragment0274681Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0274681Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '0', '1', '6', '9', '9', '6', '6', '5', '6', '3', '7', '7'])
noncomputable def fragment0274681Acc00900 : List (String × SourceJson) := (fragment0274681Field008Key00, fragment0274681Field008Value00) :: fragment0274681Acc00800
noncomputable def fragment0274681Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '1', '0', '1', '6', '9', '9', '6', '6', '5', '6', '3', '7', '7', '"', ',']

theorem object_fragment0274681_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 185) (SourceJson.white (fragment0274681Field008Chars00 ++ tail)) fragment0274681Acc00800 =
      SourceJson.object (fuel + 184) (SourceJson.white tail) fragment0274681Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_008"
  err.flush

noncomputable def fragment0274681Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0274681Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '6', '8', '3', '9', '8', '9', '9', '1', '2', '8', '4', '4', '2', '3'])
noncomputable def fragment0274681Acc01000 : List (String × SourceJson) := (fragment0274681Field009Key00, fragment0274681Field009Value00) :: fragment0274681Acc00900
noncomputable def fragment0274681Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '6', '8', '3', '9', '8', '9', '9', '1', '2', '8', '4', '4', '2', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0274681_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 184) (SourceJson.white (fragment0274681Field009Chars00 ++ tail)) fragment0274681Acc00900 =
      .ok (.obj (fragment0274681Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0274681_object_field_009"
  err.flush

noncomputable def fragment0274681Chars : List Char := '{' :: (fragment0274681Field000Chars00 ++ fragment0274681Field001Chars00 ++ fragment0274681Field002Chars00 ++ fragment0274681Field003Chars00 ++ fragment0274681Field004Chars00 ++ fragment0274681Field005Chars00 ++ fragment0274681Field006Chars00 ++ fragment0274681Field007Chars00 ++ fragment0274681Field008Chars00 ++ fragment0274681Field009Chars00)
noncomputable def fragment0274681Value : SourceJson := .obj (fragment0274681Acc01000.reverse)

theorem value_fragment0274681 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 194) (fragment0274681Chars ++ tail) =
      .ok (fragment0274681Value, tail) := by
  have hinput : fragment0274681Chars ++ tail = '{' :: (fragment0274681Field000Chars00 ++ (fragment0274681Field001Chars00 ++ (fragment0274681Field002Chars00 ++ (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0274681Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 194) (fragment0274681Chars ++ tail) =
        SourceJson.value (fuel + 194) ('{' :: (fragment0274681Field000Chars00 ++ (fragment0274681Field001Chars00 ++ (fragment0274681Field002Chars00 ++ (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 194)) hinput
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0274681Field000Chars00 ++ (fragment0274681Field001Chars00 ++ (fragment0274681Field002Chars00 ++ (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))))))))) fragment0274681Acc00000 := by rfl
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0274681Field001Chars00 ++ (fragment0274681Field002Chars00 ++ (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))))))))) fragment0274681Acc00100 := object_fragment0274681_field_000 fuel (fragment0274681Field001Chars00 ++ (fragment0274681Field002Chars00 ++ (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0274681Field002Chars00 ++ (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))))))) fragment0274681Acc00200 := object_fragment0274681_field_001 fuel (fragment0274681Field002Chars00 ++ (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 190) (SourceJson.white (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))))))) fragment0274681Acc00300 := object_fragment0274681_field_002 fuel (fragment0274681Field003Chars00 ++ (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 189) (SourceJson.white (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))))) fragment0274681Acc00400 := object_fragment0274681_field_003 fuel (fragment0274681Field004Chars00 ++ (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 188) (SourceJson.white (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))))) fragment0274681Acc00500 := object_fragment0274681_field_004 fuel (fragment0274681Field005Chars00 ++ (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 187) (SourceJson.white (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))) fragment0274681Acc00600 := object_fragment0274681_field_005 fuel (fragment0274681Field006Chars00 ++ (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 186) (SourceJson.white (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))) fragment0274681Acc00700 := object_fragment0274681_field_006 fuel (fragment0274681Field007Chars00 ++ (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 185) (SourceJson.white (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))) fragment0274681Acc00800 := object_fragment0274681_field_007 fuel (fragment0274681Field008Chars00 ++ (fragment0274681Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 184) (SourceJson.white (fragment0274681Field009Chars00 ++ (tail))) fragment0274681Acc00900 := object_fragment0274681_field_008 fuel (fragment0274681Field009Chars00 ++ (tail))
    _ = .ok (fragment0274681Value, tail) := object_fragment0274681_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_before_reader"
  err.flush

noncomputable def chunk0028LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0028SuffixChars00 : List Char := [',']
noncomputable def chunk0028Chars00 : List Char := chunk0028LeadChars00 ++ fragment0273150Chars ++ chunk0028SuffixChars00
noncomputable def chunk0028Push00 (acc : List SourceJson) : List SourceJson := fragment0273150Value :: acc

noncomputable def chunk0028AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0028_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 576)
      (SourceJson.white (chunk0028LeadChars00 ++ (fragment0273150Chars ++ rest))) acc =
      (SourceJson.value (fuel + 575) (fragment0273150Chars ++ rest)).bind
        (chunk0028AfterValue00 (fuel + 575) acc) := by rfl

theorem array_chunk0028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 576) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 575) (SourceJson.white tail) (chunk0028Push00 acc) := by
  have hinput : chunk0028Chars00 ++ tail = chunk0028LeadChars00 ++ (fragment0273150Chars ++ (chunk0028SuffixChars00 ++ tail)) := by
    simp only [chunk0028Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 576) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 576)
          (SourceJson.white (chunk0028LeadChars00 ++ (fragment0273150Chars ++ (chunk0028SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 576) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 575) (fragment0273150Chars ++ (chunk0028SuffixChars00 ++ tail))).bind
        (chunk0028AfterValue00 (fuel + 575) acc) := array_chunk0028_head fuel (chunk0028SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0273150Value, chunk0028SuffixChars00 ++ tail)).bind
        (chunk0028AfterValue00 (fuel + 575) acc) :=
      congrArg (fun result => result.bind (chunk0028AfterValue00 (fuel + 575) acc))
        (value_fragment0273150 (fuel + 371) (chunk0028SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 575) (SourceJson.white tail) (chunk0028Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_before_reader"
  err.flush

noncomputable def chunk0029LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0029SuffixChars00 : List Char := [',']
noncomputable def chunk0029Chars00 : List Char := chunk0029LeadChars00 ++ fragment0274681Chars ++ chunk0029SuffixChars00
noncomputable def chunk0029Push00 (acc : List SourceJson) : List SourceJson := fragment0274681Value :: acc

noncomputable def chunk0029AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0029_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 575)
      (SourceJson.white (chunk0029LeadChars00 ++ (fragment0274681Chars ++ rest))) acc =
      (SourceJson.value (fuel + 574) (fragment0274681Chars ++ rest)).bind
        (chunk0029AfterValue00 (fuel + 574) acc) := by rfl

theorem array_chunk0029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 575) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 574) (SourceJson.white tail) (chunk0029Push00 acc) := by
  have hinput : chunk0029Chars00 ++ tail = chunk0029LeadChars00 ++ (fragment0274681Chars ++ (chunk0029SuffixChars00 ++ tail)) := by
    simp only [chunk0029Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 575) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 575)
          (SourceJson.white (chunk0029LeadChars00 ++ (fragment0274681Chars ++ (chunk0029SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 575) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 574) (fragment0274681Chars ++ (chunk0029SuffixChars00 ++ tail))).bind
        (chunk0029AfterValue00 (fuel + 574) acc) := array_chunk0029_head fuel (chunk0029SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0274681Value, chunk0029SuffixChars00 ++ tail)).bind
        (chunk0029AfterValue00 (fuel + 574) acc) :=
      congrArg (fun result => result.bind (chunk0029AfterValue00 (fuel + 574) acc))
        (value_fragment0274681 (fuel + 380) (chunk0029SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 574) (SourceJson.white tail) (chunk0029Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0028Chars00 ++ chunk0029Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0029Push00 (chunk0028Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 576) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 574) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0028Chars00 ++ (chunk0029Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 576) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 576) (SourceJson.white (chunk0028Chars00 ++ (chunk0029Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 576) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 575) (SourceJson.white (chunk0029Chars00 ++ (tail))) (chunk0028Push00 (acc)) := array_chunk0028 fuel (chunk0029Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 574) (SourceJson.white tail) (blockPush acc) := array_chunk0029 fuel (tail) (chunk0028Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 273144).take 3047 = blockChars := by rfl

theorem block_original_split : sourceRest 273144 = blockChars ++ sourceRest 276191 := by
  calc
    sourceRest 273144 = (sourceRest 273144).take 3047 ++ (sourceRest 273144).drop 3047 :=
      (List.take_append_drop 3047 (sourceRest 273144)).symm
    _ = blockChars ++ (sourceRest 273144).drop 3047 :=
      congrArg (fun part => part ++ (sourceRest 273144).drop 3047) block_original_prefix
    _ = blockChars ++ sourceRest 276191 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 273144 3047)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 576) (SourceJson.white (sourceRest 273144)) acc =
      SourceJson.array (fuel + 574) (SourceJson.white (sourceRest 276191)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 576) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 276191) acc)

#print axioms object_fragment0273150_field_000
#print axioms object_fragment0273150_field_001
#print axioms object_fragment0273150_field_002
#print axioms object_fragment0273150_field_003
#print axioms object_fragment0273150_field_004
#print axioms object_fragment0273150_field_005
#print axioms object_fragment0273150_field_006
#print axioms object_fragment0273150_field_007
#print axioms object_fragment0273150_field_008
#print axioms object_fragment0273150_field_009
#print axioms value_fragment0273150
#print axioms object_fragment0274681_field_000
#print axioms object_fragment0274681_field_001
#print axioms object_fragment0274681_field_002
#print axioms object_fragment0274681_field_003
#print axioms object_fragment0274681_field_004
#print axioms object_fragment0274681_field_005
#print axioms object_fragment0274681_field_006
#print axioms object_fragment0274681_field_007
#print axioms object_fragment0274681_field_008
#print axioms object_fragment0274681_field_009
#print axioms value_fragment0274681
#print axioms array_chunk0028_head
#print axioms array_chunk0028
#print axioms array_chunk0029_head
#print axioms array_chunk0029
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock014

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
