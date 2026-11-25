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

namespace SimplicesBlock055

noncomputable def fragment0410422Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0410422Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0410422Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '8'])
noncomputable def fragment0410422Acc00100 : List (String × SourceJson) := (fragment0410422Field000Key00, fragment0410422Field000Value00) :: fragment0410422Acc00000
noncomputable def fragment0410422Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '8', ',']

theorem object_fragment0410422_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0410422Field000Chars00 ++ tail)) fragment0410422Acc00000 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0410422Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_000"
  err.flush

noncomputable def fragment0410422Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0410422Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0410422Acc00200 : List (String × SourceJson) := (fragment0410422Field001Key00, fragment0410422Field001Value00) :: fragment0410422Acc00100
noncomputable def fragment0410422Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0410422_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0410422Field001Chars00 ++ tail)) fragment0410422Acc00100 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0410422Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_001"
  err.flush

noncomputable def fragment0410422Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0410422Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '1', '9', '2', '3', '2', '4', '7', '4', '3', '7', '2', '1', '6', '1', '8', '0', '1', '5', '3', '1', '1', '7', '1', '0', '0', '8', '5', '7', '4', '1', '7', '8', '3', '/', '1', '6', '2', '8', '8', '8', '7', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0410422Acc00300 : List (String × SourceJson) := (fragment0410422Field002Key00, fragment0410422Field002Value00) :: fragment0410422Acc00200
noncomputable def fragment0410422Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '1', '9', '2', '3', '2', '4', '7', '4', '3', '7', '2', '1', '6', '1', '8', '0', '1', '5', '3', '1', '1', '7', '1', '0', '0', '8', '5', '7', '4', '1', '7', '8', '3', '/', '1', '6', '2', '8', '8', '8', '7', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0410422_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0410422Field002Chars00 ++ tail)) fragment0410422Acc00200 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0410422Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_002"
  err.flush

noncomputable def fragment0410422Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0410422Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0410422Acc00400 : List (String × SourceJson) := (fragment0410422Field003Key00, fragment0410422Field003Value00) :: fragment0410422Acc00300
noncomputable def fragment0410422Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0410422_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0410422Field003Chars00 ++ tail)) fragment0410422Acc00300 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0410422Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_003"
  err.flush

noncomputable def fragment0410422Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0410422Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0410422Acc00500 : List (String × SourceJson) := (fragment0410422Field004Key00, fragment0410422Field004Value00) :: fragment0410422Acc00400
noncomputable def fragment0410422Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0410422_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0410422Field004Chars00 ++ tail)) fragment0410422Acc00400 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0410422Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_004"
  err.flush

noncomputable def fragment0410422Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0410422Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '6', '6', '4', '1', '2', '8', '1', '9', '1', '9', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '8', '2', '9', '7', '4', '8', '1', '0', '7', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '7', '7', '6', '1', '3', '9', '4', '3', '7', '/', '1', '6', '2', '7', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '7', '9', '7', '2', '6', '6', '0', '2', '8', '7', '/', '5', '2', '9', '0', '7', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '6', '1', '9', '9', '2', '9', '3', '/', '3', '8', '9', '0', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '8', '3', '9', '0', '2', '8', '3', '3', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '1', '8', '0', '8', '0', '2', '7', '/', '5', '5', '6', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '7', '9', '8', '3', '3', '9', '5', '6', '1', '/', '2', '6', '4', '5', '3', '7', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '0', '9', '1', '8', '7', '0', '8', '0', '3', '9', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '3', '6', '6', '9', '1', '8', '8', '7', '/', '4', '2', '3', '2', '5', '9', '2', '0', '0', '0', '0', '0'])]
noncomputable def fragment0410422Acc00600 : List (String × SourceJson) := (fragment0410422Field005Key00, fragment0410422Field005Value00) :: fragment0410422Acc00500
noncomputable def fragment0410422Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '6', '4', '1', '2', '8', '1', '9', '1', '9', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '8', '2', '9', '7', '4', '8', '1', '0', '7', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '7', '7', '6', '1', '3', '9', '4', '3', '7', '/', '1', '6', '2', '7', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '7', '9', '7', '2', '6', '6', '0', '2', '8', '7', '/', '5', '2', '9', '0', '7', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '6', '1', '9', '9', '2', '9', '3', '/', '3', '8', '9', '0', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '2', '8', '3', '9', '0', '2', '8', '3', '3', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '1', '8', '0', '8', '0', '2', '7', '/', '5', '5', '6', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '7', '9', '8', '3', '3', '9', '5', '6', '1', '/', '2', '6', '4', '5', '3', '7', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '9', '1', '8', '7', '0', '8', '0', '3', '9', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '3', '6', '6', '9', '1', '8', '8', '7', '/', '4', '2', '3', '2', '5', '9', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0410422_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0410422Field005Chars00 ++ tail)) fragment0410422Acc00500 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0410422Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_005"
  err.flush

noncomputable def fragment0410422Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0410422Field006Value00 : SourceJson := .str (String.ofList ['3', '9', '9', '9', '2', '8', '0', '2', '0', '8', '2', '4', '2', '5', '3', '7', '7', '0', '3', '0', '1', '5', '8', '8', '9', '8', '7', '3', '7', '0', '3', '7', '7', '1', '4', '0', '9', '2', '8', '5', '2', '3', '5', '8', '4', '0', '0', '0', '0', '/', '1', '1', '9', '5', '6', '0', '9', '2', '5', '5', '7', '2', '0', '5', '8', '0', '2', '4', '4', '7', '3', '6', '0', '0', '7', '7', '3', '0', '1', '5', '4', '2', '7', '1', '9', '2', '4', '4', '7', '2', '6', '5', '7', '4', '6', '8', '5', '7', '1', '5', '9', '2', '3', '5', '9', '4', '7', '9', '5', '3', '3', '3', '2', '9', '9'])
noncomputable def fragment0410422Acc00700 : List (String × SourceJson) := (fragment0410422Field006Key00, fragment0410422Field006Value00) :: fragment0410422Acc00600
noncomputable def fragment0410422Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '9', '9', '9', '2', '8', '0', '2', '0', '8', '2', '4', '2', '5', '3', '7', '7', '0', '3', '0', '1', '5', '8', '8', '9', '8', '7', '3', '7', '0', '3', '7', '7', '1', '4', '0', '9', '2', '8', '5', '2', '3', '5', '8', '4', '0', '0', '0', '0', '/', '1', '1', '9', '5', '6', '0', '9', '2', '5', '5', '7', '2', '0', '5', '8', '0', '2', '4', '4', '7', '3', '6', '0', '0', '7', '7', '3', '0', '1', '5', '4', '2', '7', '1', '9', '2', '4', '4', '7', '2', '6', '5', '7', '4', '6', '8', '5', '7', '1', '5', '9', '2', '3', '5', '9', '4', '7', '9', '5', '3', '3', '3', '2', '9', '9', '"', ',']

theorem object_fragment0410422_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0410422Field006Chars00 ++ tail)) fragment0410422Acc00600 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0410422Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_006"
  err.flush

noncomputable def fragment0410422Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0410422Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '2', '2', '8', '5', '7', '7', '7', '9', '1', '7', '3', '0', '2', '9', '9', '1', '1', '4', '8', '0', '0', '5', '3', '5', '0', '5', '5', '9', '4', '8', '0', '3', '6', '3', '9', '7', '0', '8', '2', '8', '3', '5', '5', '1', '7', '6', '7', '9', '5', '9', '4', '6', '3', '7', '6', '9', '2', '8', '1', '8', '1', '4', '8', '6', '3', '1', '2', '1', '5', '3', '2', '3', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '8', '5', '9', '1', '9', '4', '9', '6', '9', '4', '5', '7', '2', '1', '4', '9', '1', '1', '9', '2', '5', '9', '4', '3', '5', '3', '8', '2', '7', '5', '6', '9', '1', '7', '9', '8', '1', '3', '3', '1', '4', '7', '2', '6', '9', '1', '5', '3', '0', '6', '8', '4', '8', '1', '6', '7', '5', '1', '2', '3', '1', '0', '8', '1', '9', '0', '1', '8', '2', '5', '4', '1', '9', '9', '9', '8', '0', '3', '2', '6', '7', '3', '9', '0', '7', '5', '0', '3', '2', '8', '3', '1', '8', '7', '0', '3', '1', '8', '7', '9', '0', '7'])
noncomputable def fragment0410422Acc00800 : List (String × SourceJson) := (fragment0410422Field007Key00, fragment0410422Field007Value00) :: fragment0410422Acc00700
noncomputable def fragment0410422Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '2', '2', '8', '5', '7', '7', '7', '9', '1', '7', '3', '0', '2', '9', '9', '1', '1', '4', '8', '0', '0', '5', '3', '5', '0', '5', '5', '9', '4', '8', '0', '3', '6', '3', '9', '7', '0', '8', '2', '8', '3', '5', '5', '1', '7', '6', '7', '9', '5', '9', '4', '6', '3', '7', '6', '9', '2', '8', '1', '8', '1', '4', '8', '6', '3', '1', '2', '1', '5', '3', '2', '3', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '8', '5', '9', '1', '9', '4', '9', '6', '9', '4', '5', '7', '2', '1', '4', '9', '1', '1', '9', '2', '5', '9', '4', '3', '5', '3', '8', '2', '7', '5', '6', '9', '1', '7', '9', '8', '1', '3', '3', '1', '4', '7', '2', '6', '9', '1', '5', '3', '0', '6', '8', '4', '8', '1', '6', '7', '5', '1', '2', '3', '1', '0', '8', '1', '9', '0', '1', '8', '2', '5', '4', '1', '9', '9', '9', '8', '0', '3', '2', '6', '7', '3', '9', '0', '7', '5', '0', '3', '2', '8', '3', '1', '8', '7', '0', '3', '1', '8', '7', '9', '0', '7', '"', ',']

theorem object_fragment0410422_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0410422Field007Chars00 ++ tail)) fragment0410422Acc00700 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0410422Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_007"
  err.flush

noncomputable def fragment0410422Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0410422Field008Value00 : SourceJson := .str (String.ofList ['2', '6', '5', '0', '1', '6', '0', '3', '3', '2', '5', '8', '9', '2'])
noncomputable def fragment0410422Acc00900 : List (String × SourceJson) := (fragment0410422Field008Key00, fragment0410422Field008Value00) :: fragment0410422Acc00800
noncomputable def fragment0410422Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '5', '0', '1', '6', '0', '3', '3', '2', '5', '8', '9', '2', '"', ',']

theorem object_fragment0410422_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0410422Field008Chars00 ++ tail)) fragment0410422Acc00800 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0410422Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_008"
  err.flush

noncomputable def fragment0410422Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0410422Field009Value00 : SourceJson := .str (String.ofList ['1', '9', '9', '0', '0', '1', '2', '7', '7', '4', '4', '5', '9', '5', '4'])
noncomputable def fragment0410422Acc01000 : List (String × SourceJson) := (fragment0410422Field009Key00, fragment0410422Field009Value00) :: fragment0410422Acc00900
noncomputable def fragment0410422Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '9', '0', '0', '1', '2', '7', '7', '4', '4', '5', '9', '5', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0410422_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0410422Field009Chars00 ++ tail)) fragment0410422Acc00900 =
      .ok (.obj (fragment0410422Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0410422_object_field_009"
  err.flush

noncomputable def fragment0410422Chars : List Char := '{' :: (fragment0410422Field000Chars00 ++ fragment0410422Field001Chars00 ++ fragment0410422Field002Chars00 ++ fragment0410422Field003Chars00 ++ fragment0410422Field004Chars00 ++ fragment0410422Field005Chars00 ++ fragment0410422Field006Chars00 ++ fragment0410422Field007Chars00 ++ fragment0410422Field008Chars00 ++ fragment0410422Field009Chars00)
noncomputable def fragment0410422Value : SourceJson := .obj (fragment0410422Acc01000.reverse)

theorem value_fragment0410422 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 204) (fragment0410422Chars ++ tail) =
      .ok (fragment0410422Value, tail) := by
  have hinput : fragment0410422Chars ++ tail = '{' :: (fragment0410422Field000Chars00 ++ (fragment0410422Field001Chars00 ++ (fragment0410422Field002Chars00 ++ (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0410422Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 204) (fragment0410422Chars ++ tail) =
        SourceJson.value (fuel + 204) ('{' :: (fragment0410422Field000Chars00 ++ (fragment0410422Field001Chars00 ++ (fragment0410422Field002Chars00 ++ (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 204)) hinput
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0410422Field000Chars00 ++ (fragment0410422Field001Chars00 ++ (fragment0410422Field002Chars00 ++ (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))))))))) fragment0410422Acc00000 := by rfl
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0410422Field001Chars00 ++ (fragment0410422Field002Chars00 ++ (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))))))))) fragment0410422Acc00100 := object_fragment0410422_field_000 fuel (fragment0410422Field001Chars00 ++ (fragment0410422Field002Chars00 ++ (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0410422Field002Chars00 ++ (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))))))) fragment0410422Acc00200 := object_fragment0410422_field_001 fuel (fragment0410422Field002Chars00 ++ (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))))))) fragment0410422Acc00300 := object_fragment0410422_field_002 fuel (fragment0410422Field003Chars00 ++ (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))))) fragment0410422Acc00400 := object_fragment0410422_field_003 fuel (fragment0410422Field004Chars00 ++ (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))))) fragment0410422Acc00500 := object_fragment0410422_field_004 fuel (fragment0410422Field005Chars00 ++ (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))) fragment0410422Acc00600 := object_fragment0410422_field_005 fuel (fragment0410422Field006Chars00 ++ (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))) fragment0410422Acc00700 := object_fragment0410422_field_006 fuel (fragment0410422Field007Chars00 ++ (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))) fragment0410422Acc00800 := object_fragment0410422_field_007 fuel (fragment0410422Field008Chars00 ++ (fragment0410422Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0410422Field009Chars00 ++ (tail))) fragment0410422Acc00900 := object_fragment0410422_field_008 fuel (fragment0410422Field009Chars00 ++ (tail))
    _ = .ok (fragment0410422Value, tail) := object_fragment0410422_field_009 fuel (tail)

noncomputable def fragment0411961Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0411961Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0411961Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '9'])
noncomputable def fragment0411961Acc00100 : List (String × SourceJson) := (fragment0411961Field000Key00, fragment0411961Field000Value00) :: fragment0411961Acc00000
noncomputable def fragment0411961Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '9', ',']

theorem object_fragment0411961_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0411961Field000Chars00 ++ tail)) fragment0411961Acc00000 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0411961Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_000"
  err.flush

noncomputable def fragment0411961Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0411961Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0411961Acc00200 : List (String × SourceJson) := (fragment0411961Field001Key00, fragment0411961Field001Value00) :: fragment0411961Acc00100
noncomputable def fragment0411961Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0411961_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0411961Field001Chars00 ++ tail)) fragment0411961Acc00100 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0411961Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_001"
  err.flush

noncomputable def fragment0411961Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0411961Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '4', '6', '3', '1', '5', '5', '6', '6', '6', '6', '1', '6', '3', '2', '4', '3', '8', '7', '7', '1', '3', '5', '4', '8', '1', '1', '8', '0', '1', '2', '2', '1', '2', '0', '6', '7', '/', '7', '4', '6', '4', '3', '7', '6', '7', '3', '7', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0411961Acc00300 : List (String × SourceJson) := (fragment0411961Field002Key00, fragment0411961Field002Value00) :: fragment0411961Acc00200
noncomputable def fragment0411961Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '4', '6', '3', '1', '5', '5', '6', '6', '6', '6', '1', '6', '3', '2', '4', '3', '8', '7', '7', '1', '3', '5', '4', '8', '1', '1', '8', '0', '1', '2', '2', '1', '2', '0', '6', '7', '/', '7', '4', '6', '4', '3', '7', '6', '7', '3', '7', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0411961_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0411961Field002Chars00 ++ tail)) fragment0411961Acc00200 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0411961Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_002"
  err.flush

noncomputable def fragment0411961Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0411961Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0411961Acc00400 : List (String × SourceJson) := (fragment0411961Field003Key00, fragment0411961Field003Value00) :: fragment0411961Acc00300
noncomputable def fragment0411961Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0411961_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0411961Field003Chars00 ++ tail)) fragment0411961Acc00300 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0411961Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_003"
  err.flush

noncomputable def fragment0411961Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0411961Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0411961Acc00500 : List (String × SourceJson) := (fragment0411961Field004Key00, fragment0411961Field004Value00) :: fragment0411961Acc00400
noncomputable def fragment0411961Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0411961_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0411961Field004Chars00 ++ tail)) fragment0411961Acc00400 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0411961Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_004"
  err.flush

noncomputable def fragment0411961Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0411961Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '8', '8', '0', '1', '4', '5', '2', '0', '2', '0', '8', '9', '9', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '3', '6', '0', '0', '3', '1', '1', '2', '9', '2', '5', '9', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '0', '5', '5', '0', '3', '8', '4', '6', '4', '0', '0', '3', '/', '3', '8', '2', '5', '6', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '7', '8', '0', '0', '3', '7', '6', '1', '5', '3', '3', '/', '2', '4', '8', '6', '6', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '1', '1', '9', '5', '1', '9', '8', '3', '9', '4', '7', '/', '2', '9', '2', '5', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '8', '6', '3', '5', '7', '8', '4', '0', '6', '1', '6', '9', '7', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '6', '3', '5', '3', '0', '9', '3', '3', '8', '9', '/', '5', '2', '3', '5', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '3', '4', '9', '5', '9', '3', '0', '8', '7', '1', '0', '7', '/', '9', '9', '4', '6', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '8', '2', '4', '5', '2', '6', '1', '5', '6', '7', '3', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '8', '2', '3', '8', '6', '3', '0', '5', '0', '6', '5', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0411961Acc00600 : List (String × SourceJson) := (fragment0411961Field005Key00, fragment0411961Field005Value00) :: fragment0411961Acc00500
noncomputable def fragment0411961Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '8', '0', '1', '4', '5', '2', '0', '2', '0', '8', '9', '9', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '3', '6', '0', '0', '3', '1', '1', '2', '9', '2', '5', '9', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '0', '5', '5', '0', '3', '8', '4', '6', '4', '0', '0', '3', '/', '3', '8', '2', '5', '6', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '7', '8', '0', '0', '3', '7', '6', '1', '5', '3', '3', '/', '2', '4', '8', '6', '6', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '1', '1', '9', '5', '1', '9', '8', '3', '9', '4', '7', '/', '2', '9', '2', '5', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '8', '6', '3', '5', '7', '8', '4', '0', '6', '1', '6', '9', '7', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '6', '3', '5', '3', '0', '9', '3', '3', '8', '9', '/', '5', '2', '3', '5', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '3', '4', '9', '5', '9', '3', '0', '8', '7', '1', '0', '7', '/', '9', '9', '4', '6', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '8', '2', '4', '5', '2', '6', '1', '5', '6', '7', '3', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '8', '2', '3', '8', '6', '3', '0', '5', '0', '6', '5', '3', '/', '4', '9', '7', '3', '2', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0411961_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0411961Field005Chars00 ++ tail)) fragment0411961Acc00500 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0411961Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_005"
  err.flush

noncomputable def fragment0411961Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0411961Field006Value00 : SourceJson := .str (String.ofList ['3', '4', '7', '8', '3', '1', '6', '7', '5', '3', '2', '1', '4', '3', '8', '2', '0', '7', '4', '0', '9', '4', '9', '5', '8', '6', '7', '4', '3', '4', '0', '0', '0', '1', '9', '9', '4', '7', '1', '1', '5', '1', '6', '0', '0', '0', '0', '0', '/', '4', '7', '9', '0', '4', '0', '2', '7', '7', '8', '1', '0', '8', '6', '4', '8', '8', '3', '4', '1', '6', '6', '4', '1', '7', '8', '7', '8', '9', '8', '1', '8', '2', '8', '9', '3', '6', '8', '5', '6', '4', '0', '7', '0', '1', '4', '0', '9', '5', '4', '2', '1', '5', '0', '3', '4', '7', '2', '0', '9', '0', '2', '1', '3'])
noncomputable def fragment0411961Acc00700 : List (String × SourceJson) := (fragment0411961Field006Key00, fragment0411961Field006Value00) :: fragment0411961Acc00600
noncomputable def fragment0411961Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '7', '8', '3', '1', '6', '7', '5', '3', '2', '1', '4', '3', '8', '2', '0', '7', '4', '0', '9', '4', '9', '5', '8', '6', '7', '4', '3', '4', '0', '0', '0', '1', '9', '9', '4', '7', '1', '1', '5', '1', '6', '0', '0', '0', '0', '0', '/', '4', '7', '9', '0', '4', '0', '2', '7', '7', '8', '1', '0', '8', '6', '4', '8', '8', '3', '4', '1', '6', '6', '4', '1', '7', '8', '7', '8', '9', '8', '1', '8', '2', '8', '9', '3', '6', '8', '5', '6', '4', '0', '7', '0', '1', '4', '0', '9', '5', '4', '2', '1', '5', '0', '3', '4', '7', '2', '0', '9', '0', '2', '1', '3', '"', ',']

theorem object_fragment0411961_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0411961Field006Chars00 ++ tail)) fragment0411961Acc00600 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0411961Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_006"
  err.flush

noncomputable def fragment0411961Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0411961Field007Value00 : SourceJson := .str (String.ofList ['6', '4', '8', '1', '2', '5', '9', '3', '4', '0', '6', '0', '6', '3', '8', '2', '2', '5', '8', '0', '8', '3', '0', '4', '1', '4', '1', '0', '9', '3', '1', '4', '3', '4', '9', '9', '3', '3', '7', '4', '5', '7', '7', '7', '7', '8', '6', '3', '5', '8', '0', '1', '9', '5', '7', '0', '4', '0', '0', '4', '6', '7', '3', '3', '0', '3', '6', '3', '5', '3', '7', '4', '4', '0', '6', '5', '1', '3', '1', '3', '5', '8', '2', '3', '6', '7', '3', '1', '0', '6', '2', '9', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '8', '6', '5', '7', '9', '2', '8', '7', '0', '5', '3', '9', '7', '0', '2', '2', '3', '4', '8', '2', '3', '9', '0', '9', '6', '5', '0', '3', '9', '8', '2', '5', '5', '4', '8', '1', '3', '7', '1', '4', '6', '4', '2', '0', '9', '0', '2', '2', '3', '8', '6', '8', '9', '4', '7', '7', '7', '2', '6', '1', '2', '8', '1', '8', '1', '0', '9', '7', '6', '1', '9', '1', '5', '6', '7', '0', '8', '9', '4', '9', '9', '8', '3', '5', '3', '1', '9', '2', '1', '4', '6', '4', '9', '4', '7', '8', '8', '8', '9', '2', '5', '7', '3', '4', '2', '7', '9', '5', '6', '5', '8', '4', '3', '7', '9', '0', '8', '6', '7', '7', '2', '4', '0', '2', '2', '1', '0', '2', '8', '2', '9', '7'])
noncomputable def fragment0411961Acc00800 : List (String × SourceJson) := (fragment0411961Field007Key00, fragment0411961Field007Value00) :: fragment0411961Acc00700
noncomputable def fragment0411961Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '4', '8', '1', '2', '5', '9', '3', '4', '0', '6', '0', '6', '3', '8', '2', '2', '5', '8', '0', '8', '3', '0', '4', '1', '4', '1', '0', '9', '3', '1', '4', '3', '4', '9', '9', '3', '3', '7', '4', '5', '7', '7', '7', '7', '8', '6', '3', '5', '8', '0', '1', '9', '5', '7', '0', '4', '0', '0', '4', '6', '7', '3', '3', '0', '3', '6', '3', '5', '3', '7', '4', '4', '0', '6', '5', '1', '3', '1', '3', '5', '8', '2', '3', '6', '7', '3', '1', '0', '6', '2', '9', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '8', '6', '5', '7', '9', '2', '8', '7', '0', '5', '3', '9', '7', '0', '2', '2', '3', '4', '8', '2', '3', '9', '0', '9', '6', '5', '0', '3', '9', '8', '2', '5', '5', '4', '8', '1', '3', '7', '1', '4', '6', '4', '2', '0', '9', '0', '2', '2', '3', '8', '6', '8', '9', '4', '7', '7', '7', '2', '6', '1', '2', '8', '1', '8', '1', '0', '9', '7', '6', '1', '9', '1', '5', '6', '7', '0', '8', '9', '4', '9', '9', '8', '3', '5', '3', '1', '9', '2', '1', '4', '6', '4', '9', '4', '7', '8', '8', '8', '9', '2', '5', '7', '3', '4', '2', '7', '9', '5', '6', '5', '8', '4', '3', '7', '9', '0', '8', '6', '7', '7', '2', '4', '0', '2', '2', '1', '0', '2', '8', '2', '9', '7', '"', ',']

theorem object_fragment0411961_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0411961Field007Chars00 ++ tail)) fragment0411961Acc00700 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0411961Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_007"
  err.flush

noncomputable def fragment0411961Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0411961Field008Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '2', '7', '6', '5', '6', '3', '9', '2', '3', '0'])
noncomputable def fragment0411961Acc00900 : List (String × SourceJson) := (fragment0411961Field008Key00, fragment0411961Field008Value00) :: fragment0411961Acc00800
noncomputable def fragment0411961Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '5', '2', '7', '6', '5', '6', '3', '9', '2', '3', '0', '"', ',']

theorem object_fragment0411961_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0411961Field008Chars00 ++ tail)) fragment0411961Acc00800 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0411961Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_008"
  err.flush

noncomputable def fragment0411961Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0411961Field009Value00 : SourceJson := .str (String.ofList ['4', '3', '2', '7', '5', '5', '1', '2', '5', '5', '4', '2', '0', '6'])
noncomputable def fragment0411961Acc01000 : List (String × SourceJson) := (fragment0411961Field009Key00, fragment0411961Field009Value00) :: fragment0411961Acc00900
noncomputable def fragment0411961Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '2', '7', '5', '5', '1', '2', '5', '5', '4', '2', '0', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0411961_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0411961Field009Chars00 ++ tail)) fragment0411961Acc00900 =
      .ok (.obj (fragment0411961Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0411961_object_field_009"
  err.flush

noncomputable def fragment0411961Chars : List Char := '{' :: (fragment0411961Field000Chars00 ++ fragment0411961Field001Chars00 ++ fragment0411961Field002Chars00 ++ fragment0411961Field003Chars00 ++ fragment0411961Field004Chars00 ++ fragment0411961Field005Chars00 ++ fragment0411961Field006Chars00 ++ fragment0411961Field007Chars00 ++ fragment0411961Field008Chars00 ++ fragment0411961Field009Chars00)
noncomputable def fragment0411961Value : SourceJson := .obj (fragment0411961Acc01000.reverse)

theorem value_fragment0411961 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 264) (fragment0411961Chars ++ tail) =
      .ok (fragment0411961Value, tail) := by
  have hinput : fragment0411961Chars ++ tail = '{' :: (fragment0411961Field000Chars00 ++ (fragment0411961Field001Chars00 ++ (fragment0411961Field002Chars00 ++ (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0411961Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 264) (fragment0411961Chars ++ tail) =
        SourceJson.value (fuel + 264) ('{' :: (fragment0411961Field000Chars00 ++ (fragment0411961Field001Chars00 ++ (fragment0411961Field002Chars00 ++ (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 264)) hinput
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0411961Field000Chars00 ++ (fragment0411961Field001Chars00 ++ (fragment0411961Field002Chars00 ++ (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))))))))) fragment0411961Acc00000 := by rfl
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0411961Field001Chars00 ++ (fragment0411961Field002Chars00 ++ (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))))))))) fragment0411961Acc00100 := object_fragment0411961_field_000 fuel (fragment0411961Field001Chars00 ++ (fragment0411961Field002Chars00 ++ (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0411961Field002Chars00 ++ (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))))))) fragment0411961Acc00200 := object_fragment0411961_field_001 fuel (fragment0411961Field002Chars00 ++ (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))))))) fragment0411961Acc00300 := object_fragment0411961_field_002 fuel (fragment0411961Field003Chars00 ++ (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))))) fragment0411961Acc00400 := object_fragment0411961_field_003 fuel (fragment0411961Field004Chars00 ++ (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))))) fragment0411961Acc00500 := object_fragment0411961_field_004 fuel (fragment0411961Field005Chars00 ++ (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))) fragment0411961Acc00600 := object_fragment0411961_field_005 fuel (fragment0411961Field006Chars00 ++ (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))) fragment0411961Acc00700 := object_fragment0411961_field_006 fuel (fragment0411961Field007Chars00 ++ (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))) fragment0411961Acc00800 := object_fragment0411961_field_007 fuel (fragment0411961Field008Chars00 ++ (fragment0411961Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0411961Field009Chars00 ++ (tail))) fragment0411961Acc00900 := object_fragment0411961_field_008 fuel (fragment0411961Field009Chars00 ++ (tail))
    _ = .ok (fragment0411961Value, tail) := object_fragment0411961_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0108_before_reader"
  err.flush

noncomputable def chunk0108LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0108SuffixChars00 : List Char := [',']
noncomputable def chunk0108Chars00 : List Char := chunk0108LeadChars00 ++ fragment0410422Chars ++ chunk0108SuffixChars00
noncomputable def chunk0108Push00 (acc : List SourceJson) : List SourceJson := fragment0410422Value :: acc

noncomputable def chunk0108AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0108_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 496)
      (SourceJson.white (chunk0108LeadChars00 ++ (fragment0410422Chars ++ rest))) acc =
      (SourceJson.value (fuel + 495) (fragment0410422Chars ++ rest)).bind
        (chunk0108AfterValue00 (fuel + 495) acc) := by rfl

theorem array_chunk0108 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 496) (SourceJson.white (chunk0108Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 495) (SourceJson.white tail) (chunk0108Push00 acc) := by
  have hinput : chunk0108Chars00 ++ tail = chunk0108LeadChars00 ++ (fragment0410422Chars ++ (chunk0108SuffixChars00 ++ tail)) := by
    simp only [chunk0108Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 496) (SourceJson.white (chunk0108Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 496)
          (SourceJson.white (chunk0108LeadChars00 ++ (fragment0410422Chars ++ (chunk0108SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 496) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 495) (fragment0410422Chars ++ (chunk0108SuffixChars00 ++ tail))).bind
        (chunk0108AfterValue00 (fuel + 495) acc) := array_chunk0108_head fuel (chunk0108SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0410422Value, chunk0108SuffixChars00 ++ tail)).bind
        (chunk0108AfterValue00 (fuel + 495) acc) :=
      congrArg (fun result => result.bind (chunk0108AfterValue00 (fuel + 495) acc))
        (value_fragment0410422 (fuel + 291) (chunk0108SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 495) (SourceJson.white tail) (chunk0108Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0108_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0109_before_reader"
  err.flush

noncomputable def chunk0109LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0109SuffixChars00 : List Char := [',']
noncomputable def chunk0109Chars00 : List Char := chunk0109LeadChars00 ++ fragment0411961Chars ++ chunk0109SuffixChars00
noncomputable def chunk0109Push00 (acc : List SourceJson) : List SourceJson := fragment0411961Value :: acc

noncomputable def chunk0109AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0109_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 495)
      (SourceJson.white (chunk0109LeadChars00 ++ (fragment0411961Chars ++ rest))) acc =
      (SourceJson.value (fuel + 494) (fragment0411961Chars ++ rest)).bind
        (chunk0109AfterValue00 (fuel + 494) acc) := by rfl

theorem array_chunk0109 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 495) (SourceJson.white (chunk0109Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 494) (SourceJson.white tail) (chunk0109Push00 acc) := by
  have hinput : chunk0109Chars00 ++ tail = chunk0109LeadChars00 ++ (fragment0411961Chars ++ (chunk0109SuffixChars00 ++ tail)) := by
    simp only [chunk0109Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 495) (SourceJson.white (chunk0109Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 495)
          (SourceJson.white (chunk0109LeadChars00 ++ (fragment0411961Chars ++ (chunk0109SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 495) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 494) (fragment0411961Chars ++ (chunk0109SuffixChars00 ++ tail))).bind
        (chunk0109AfterValue00 (fuel + 494) acc) := array_chunk0109_head fuel (chunk0109SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0411961Value, chunk0109SuffixChars00 ++ tail)).bind
        (chunk0109AfterValue00 (fuel + 494) acc) :=
      congrArg (fun result => result.bind (chunk0109AfterValue00 (fuel + 494) acc))
        (value_fragment0411961 (fuel + 230) (chunk0109SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 494) (SourceJson.white tail) (chunk0109Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0109_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0108Chars00 ++ chunk0109Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0109Push00 (chunk0108Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 496) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 494) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0108Chars00 ++ (chunk0109Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 496) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 496) (SourceJson.white (chunk0108Chars00 ++ (chunk0109Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 496) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 495) (SourceJson.white (chunk0109Chars00 ++ (tail))) (chunk0108Push00 (acc)) := array_chunk0108 fuel (chunk0109Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 494) (SourceJson.white tail) (blockPush acc) := array_chunk0109 fuel (tail) (chunk0108Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 410416).take 3196 = blockChars := by rfl

theorem block_original_split : sourceRest 410416 = blockChars ++ sourceRest 413612 := by
  calc
    sourceRest 410416 = (sourceRest 410416).take 3196 ++ (sourceRest 410416).drop 3196 :=
      (List.take_append_drop 3196 (sourceRest 410416)).symm
    _ = blockChars ++ (sourceRest 410416).drop 3196 :=
      congrArg (fun part => part ++ (sourceRest 410416).drop 3196) block_original_prefix
    _ = blockChars ++ sourceRest 413612 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 410416 3196)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 496) (SourceJson.white (sourceRest 410416)) acc =
      SourceJson.array (fuel + 494) (SourceJson.white (sourceRest 413612)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 496) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 413612) acc)

#print axioms object_fragment0410422_field_000
#print axioms object_fragment0410422_field_001
#print axioms object_fragment0410422_field_002
#print axioms object_fragment0410422_field_003
#print axioms object_fragment0410422_field_004
#print axioms object_fragment0410422_field_005
#print axioms object_fragment0410422_field_006
#print axioms object_fragment0410422_field_007
#print axioms object_fragment0410422_field_008
#print axioms object_fragment0410422_field_009
#print axioms value_fragment0410422
#print axioms object_fragment0411961_field_000
#print axioms object_fragment0411961_field_001
#print axioms object_fragment0411961_field_002
#print axioms object_fragment0411961_field_003
#print axioms object_fragment0411961_field_004
#print axioms object_fragment0411961_field_005
#print axioms object_fragment0411961_field_006
#print axioms object_fragment0411961_field_007
#print axioms object_fragment0411961_field_008
#print axioms object_fragment0411961_field_009
#print axioms value_fragment0411961
#print axioms array_chunk0108_head
#print axioms array_chunk0108
#print axioms array_chunk0109_head
#print axioms array_chunk0109
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock055

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
