import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock005

noncomputable def fragment0173580Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0173580Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0173580Field000Value00 : SourceJson := .number (String.ofList ['4', '0'])
noncomputable def fragment0173580Acc00100 : List (String × SourceJson) := (fragment0173580Field000Key00, fragment0173580Field000Value00) :: fragment0173580Acc00000
noncomputable def fragment0173580Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '0', ',']

theorem object_fragment0173580_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 293) (SourceJson.white (fragment0173580Field000Chars00 ++ tail)) fragment0173580Acc00000 =
      SourceJson.object (fuel + 292) (SourceJson.white tail) fragment0173580Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_000"
  err.flush

noncomputable def fragment0173580Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0173580Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0173580Acc00200 : List (String × SourceJson) := (fragment0173580Field001Key00, fragment0173580Field001Value00) :: fragment0173580Acc00100
noncomputable def fragment0173580Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0173580_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 292) (SourceJson.white (fragment0173580Field001Chars00 ++ tail)) fragment0173580Acc00100 =
      SourceJson.object (fuel + 291) (SourceJson.white tail) fragment0173580Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_001"
  err.flush

noncomputable def fragment0173580Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0173580Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '4', '2', '6', '2', '0', '6', '1', '9', '1', '7', '1', '7', '8', '8', '3', '9', '3', '4', '8', '1', '3', '6', '8', '4', '0', '9', '1', '6', '3', '1', '8', '9', '0', '1', '2', '7', '/', '2', '0', '2', '2', '0', '8', '6', '8', '1', '9', '1', '4', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0173580Acc00300 : List (String × SourceJson) := (fragment0173580Field002Key00, fragment0173580Field002Value00) :: fragment0173580Acc00200
noncomputable def fragment0173580Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '4', '2', '6', '2', '0', '6', '1', '9', '1', '7', '1', '7', '8', '8', '3', '9', '3', '4', '8', '1', '3', '6', '8', '4', '0', '9', '1', '6', '3', '1', '8', '9', '0', '1', '2', '7', '/', '2', '0', '2', '2', '0', '8', '6', '8', '1', '9', '1', '4', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0173580_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 291) (SourceJson.white (fragment0173580Field002Chars00 ++ tail)) fragment0173580Acc00200 =
      SourceJson.object (fuel + 290) (SourceJson.white tail) fragment0173580Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_002"
  err.flush

noncomputable def fragment0173580Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0173580Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0173580Acc00400 : List (String × SourceJson) := (fragment0173580Field003Key00, fragment0173580Field003Value00) :: fragment0173580Acc00300
noncomputable def fragment0173580Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0173580_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 290) (SourceJson.white (fragment0173580Field003Chars00 ++ tail)) fragment0173580Acc00300 =
      SourceJson.object (fuel + 289) (SourceJson.white tail) fragment0173580Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_003"
  err.flush

noncomputable def fragment0173580Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0173580Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '5', '3', '1', '2', '4', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0173580Acc00500 : List (String × SourceJson) := (fragment0173580Field004Key00, fragment0173580Field004Value00) :: fragment0173580Acc00400
noncomputable def fragment0173580Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '1', '2', '4', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0173580_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 289) (SourceJson.white (fragment0173580Field004Chars00 ++ tail)) fragment0173580Acc00400 =
      SourceJson.object (fuel + 288) (SourceJson.white tail) fragment0173580Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_004"
  err.flush

noncomputable def fragment0173580Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0173580Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '9', '3', '4', '6', '9', '9', '9', '8', '9', '5', '0', '4', '9', '5', '7', '/', '2', '2', '0', '8', '2', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '3', '2', '5', '2', '1', '9', '3', '0', '9', '9', '8', '8', '9', '/', '2', '7', '6', '0', '3', '0', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '1', '9', '9', '2', '6', '3', '1', '9', '8', '6', '5', '0', '1', '/', '1', '5', '4', '5', '7', '7', '0', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '3', '2', '6', '6', '8', '0', '0', '3', '5', '0', '4', '6', '3', '3', '/', '3', '8', '6', '4', '4', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '6', '9', '1', '6', '8', '2', '8', '0', '7', '9', '5', '3', '8', '7', '/', '3', '8', '6', '4', '4', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '6', '2', '5', '7', '8', '0', '4', '7', '9', '8', '1', '6', '1', '/', '7', '7', '2', '8', '8', '5', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '8', '6', '3', '5', '2', '8', '0', '8', '3', '7', '8', '3', '1', '1', '/', '7', '7', '2', '8', '8', '5', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '3', '9', '2', '6', '4', '8', '6', '0', '3', '7', '9', '9', '/', '3', '6', '8', '0', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '1', '3', '1', '0', '1', '9', '3', '3', '5', '4', '5', '3', '/', '1', '2', '2', '6', '8', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '2', '2', '2', '4', '0', '5', '4', '3', '5', '8', '7', '/', '3', '0', '6', '7', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0173580Acc00600 : List (String × SourceJson) := (fragment0173580Field005Key00, fragment0173580Field005Value00) :: fragment0173580Acc00500
noncomputable def fragment0173580Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '4', '6', '9', '9', '9', '8', '9', '5', '0', '4', '9', '5', '7', '/', '2', '2', '0', '8', '2', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '2', '5', '2', '1', '9', '3', '0', '9', '9', '8', '8', '9', '/', '2', '7', '6', '0', '3', '0', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '1', '9', '9', '2', '6', '3', '1', '9', '8', '6', '5', '0', '1', '/', '1', '5', '4', '5', '7', '7', '0', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '3', '2', '6', '6', '8', '0', '0', '3', '5', '0', '4', '6', '3', '3', '/', '3', '8', '6', '4', '4', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '9', '1', '6', '8', '2', '8', '0', '7', '9', '5', '3', '8', '7', '/', '3', '8', '6', '4', '4', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '6', '2', '5', '7', '8', '0', '4', '7', '9', '8', '1', '6', '1', '/', '7', '7', '2', '8', '8', '5', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '6', '3', '5', '2', '8', '0', '8', '3', '7', '8', '3', '1', '1', '/', '7', '7', '2', '8', '8', '5', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '3', '9', '2', '6', '4', '8', '6', '0', '3', '7', '9', '9', '/', '3', '6', '8', '0', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '3', '1', '0', '1', '9', '3', '3', '5', '4', '5', '3', '/', '1', '2', '2', '6', '8', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '2', '2', '2', '4', '0', '5', '4', '3', '5', '8', '7', '/', '3', '0', '6', '7', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0173580_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 288) (SourceJson.white (fragment0173580Field005Chars00 ++ tail)) fragment0173580Acc00500 =
      SourceJson.object (fuel + 287) (SourceJson.white tail) fragment0173580Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_005"
  err.flush

noncomputable def fragment0173580Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0173580Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '6', '0', '9', '1', '4', '8', '9', '0', '0', '6', '6', '5', '8', '9', '7', '9', '3', '1', '7', '1', '1', '6', '2', '3', '3', '8', '1', '2', '5', '2', '8', '3', '2', '2', '5', '1', '9', '1', '9', '1', '8', '7', '1', '4', '8', '8', '0', '0', '0', '0', '0', '0', '/', '2', '4', '8', '0', '0', '7', '9', '5', '2', '3', '3', '4', '3', '3', '1', '9', '8', '1', '2', '9', '3', '6', '5', '7', '0', '0', '8', '7', '5', '7', '3', '0', '3', '2', '4', '9', '2', '8', '2', '8', '6', '5', '4', '4', '3', '1', '4', '5', '4', '5', '1', '8', '6', '8', '2', '9', '0', '9', '9', '3', '1', '4', '7', '6', '8', '5', '7'])
noncomputable def fragment0173580Acc00700 : List (String × SourceJson) := (fragment0173580Field006Key00, fragment0173580Field006Value00) :: fragment0173580Acc00600
noncomputable def fragment0173580Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '6', '0', '9', '1', '4', '8', '9', '0', '0', '6', '6', '5', '8', '9', '7', '9', '3', '1', '7', '1', '1', '6', '2', '3', '3', '8', '1', '2', '5', '2', '8', '3', '2', '2', '5', '1', '9', '1', '9', '1', '8', '7', '1', '4', '8', '8', '0', '0', '0', '0', '0', '0', '/', '2', '4', '8', '0', '0', '7', '9', '5', '2', '3', '3', '4', '3', '3', '1', '9', '8', '1', '2', '9', '3', '6', '5', '7', '0', '0', '8', '7', '5', '7', '3', '0', '3', '2', '4', '9', '2', '8', '2', '8', '6', '5', '4', '4', '3', '1', '4', '5', '4', '5', '1', '8', '6', '8', '2', '9', '0', '9', '9', '3', '1', '4', '7', '6', '8', '5', '7', '"', ',']

theorem object_fragment0173580_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 287) (SourceJson.white (fragment0173580Field006Chars00 ++ tail)) fragment0173580Acc00600 =
      SourceJson.object (fuel + 286) (SourceJson.white tail) fragment0173580Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_006"
  err.flush

noncomputable def fragment0173580Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0173580Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '4', '2', '4', '2', '7', '6', '2', '9', '5', '8', '7', '8', '8', '2', '2', '2', '4', '5', '7', '3', '2', '8', '3', '4', '3', '8', '8', '5', '3', '8', '2', '9', '6', '6', '9', '5', '9', '6', '4', '9', '1', '4', '3', '9', '1', '8', '3', '2', '2', '0', '5', '7', '2', '6', '0', '8', '1', '7', '1', '6', '5', '6', '9', '6', '8', '1', '5', '5', '0', '0', '1', '8', '3', '0', '8', '9', '1', '5', '9', '1', '5', '3', '8', '7', '1', '2', '8', '0', '1', '1', '6', '9', '7', '6', '3', '6', '9', '3', '1', '9', '3', '6', '4', '1', '0', '6', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '6', '3', '2', '4', '2', '4', '0', '4', '5', '6', '8', '4', '9', '6', '5', '2', '4', '5', '6', '3', '5', '3', '6', '3', '3', '9', '9', '6', '8', '3', '4', '7', '3', '5', '1', '5', '6', '4', '7', '7', '7', '1', '1', '2', '8', '1', '9', '0', '8', '4', '9', '5', '9', '9', '9', '3', '6', '2', '6', '0', '3', '6', '6', '7', '0', '7', '1', '8', '1', '4', '9', '6', '6', '3', '2', '0', '4', '1', '3', '8', '0', '3', '1', '8', '3', '5', '1', '4', '2', '8', '0', '2', '9', '8', '9', '7', '3', '2', '8', '4', '5', '5', '5', '3', '5', '9', '9', '7', '6', '4', '4', '3', '1', '9', '2', '2', '4', '5', '6', '5', '1', '5', '3', '0', '0', '7', '4', '3', '9', '7', '9', '7', '0', '3', '9', '3', '2', '5', '9', '3', '9', '3', '8', '7', '7'])
noncomputable def fragment0173580Acc00800 : List (String × SourceJson) := (fragment0173580Field007Key00, fragment0173580Field007Value00) :: fragment0173580Acc00700
noncomputable def fragment0173580Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '4', '2', '4', '2', '7', '6', '2', '9', '5', '8', '7', '8', '8', '2', '2', '2', '4', '5', '7', '3', '2', '8', '3', '4', '3', '8', '8', '5', '3', '8', '2', '9', '6', '6', '9', '5', '9', '6', '4', '9', '1', '4', '3', '9', '1', '8', '3', '2', '2', '0', '5', '7', '2', '6', '0', '8', '1', '7', '1', '6', '5', '6', '9', '6', '8', '1', '5', '5', '0', '0', '1', '8', '3', '0', '8', '9', '1', '5', '9', '1', '5', '3', '8', '7', '1', '2', '8', '0', '1', '1', '6', '9', '7', '6', '3', '6', '9', '3', '1', '9', '3', '6', '4', '1', '0', '6', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '6', '3', '2', '4', '2', '4', '0', '4', '5', '6', '8', '4', '9', '6', '5', '2', '4', '5', '6', '3', '5', '3', '6', '3', '3', '9', '9', '6', '8', '3', '4', '7', '3', '5', '1', '5', '6', '4', '7', '7', '7', '1', '1', '2', '8', '1', '9', '0', '8', '4', '9', '5', '9', '9', '9', '3', '6', '2', '6', '0', '3', '6', '6', '7', '0', '7', '1', '8', '1', '4', '9', '6', '6', '3', '2', '0', '4', '1', '3', '8', '0', '3', '1', '8', '3', '5', '1', '4', '2', '8', '0', '2', '9', '8', '9', '7', '3', '2', '8', '4', '5', '5', '5', '3', '5', '9', '9', '7', '6', '4', '4', '3', '1', '9', '2', '2', '4', '5', '6', '5', '1', '5', '3', '0', '0', '7', '4', '3', '9', '7', '9', '7', '0', '3', '9', '3', '2', '5', '9', '3', '9', '3', '8', '7', '7', '"', ',']

theorem object_fragment0173580_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 286) (SourceJson.white (fragment0173580Field007Chars00 ++ tail)) fragment0173580Acc00700 =
      SourceJson.object (fuel + 285) (SourceJson.white tail) fragment0173580Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_007"
  err.flush

noncomputable def fragment0173580Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0173580Field008Value00 : SourceJson := .str (String.ofList ['3', '7', '0', '8', '6', '3', '7', '2', '7', '1', '8', '9', '8', '1', '8', '0'])
noncomputable def fragment0173580Acc00900 : List (String × SourceJson) := (fragment0173580Field008Key00, fragment0173580Field008Value00) :: fragment0173580Acc00800
noncomputable def fragment0173580Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '0', '8', '6', '3', '7', '2', '7', '1', '8', '9', '8', '1', '8', '0', '"', ',']

theorem object_fragment0173580_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 285) (SourceJson.white (fragment0173580Field008Chars00 ++ tail)) fragment0173580Acc00800 =
      SourceJson.object (fuel + 284) (SourceJson.white tail) fragment0173580Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_008"
  err.flush

noncomputable def fragment0173580Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0173580Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '1', '1', '2', '4', '6', '0', '9', '1', '3', '1', '7', '0', '2', '2'])
noncomputable def fragment0173580Acc01000 : List (String × SourceJson) := (fragment0173580Field009Key00, fragment0173580Field009Value00) :: fragment0173580Acc00900
noncomputable def fragment0173580Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '1', '1', '2', '4', '6', '0', '9', '1', '3', '1', '7', '0', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0173580_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 284) (SourceJson.white (fragment0173580Field009Chars00 ++ tail)) fragment0173580Acc00900 =
      .ok (.obj (fragment0173580Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173580_object_field_009"
  err.flush

noncomputable def fragment0173580Chars : List Char := '{' :: (fragment0173580Field000Chars00 ++ fragment0173580Field001Chars00 ++ fragment0173580Field002Chars00 ++ fragment0173580Field003Chars00 ++ fragment0173580Field004Chars00 ++ fragment0173580Field005Chars00 ++ fragment0173580Field006Chars00 ++ fragment0173580Field007Chars00 ++ fragment0173580Field008Chars00 ++ fragment0173580Field009Chars00)
noncomputable def fragment0173580Value : SourceJson := .obj (fragment0173580Acc01000.reverse)

theorem value_fragment0173580 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 294) (fragment0173580Chars ++ tail) =
      .ok (fragment0173580Value, tail) := by
  have hinput : fragment0173580Chars ++ tail = '{' :: (fragment0173580Field000Chars00 ++ (fragment0173580Field001Chars00 ++ (fragment0173580Field002Chars00 ++ (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0173580Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 294) (fragment0173580Chars ++ tail) =
        SourceJson.value (fuel + 294) ('{' :: (fragment0173580Field000Chars00 ++ (fragment0173580Field001Chars00 ++ (fragment0173580Field002Chars00 ++ (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 294)) hinput
    _ = SourceJson.object (fuel + 293) (SourceJson.white (fragment0173580Field000Chars00 ++ (fragment0173580Field001Chars00 ++ (fragment0173580Field002Chars00 ++ (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))))))))) fragment0173580Acc00000 := by rfl
    _ = SourceJson.object (fuel + 292) (SourceJson.white (fragment0173580Field001Chars00 ++ (fragment0173580Field002Chars00 ++ (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))))))))) fragment0173580Acc00100 := object_fragment0173580_field_000 fuel (fragment0173580Field001Chars00 ++ (fragment0173580Field002Chars00 ++ (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 291) (SourceJson.white (fragment0173580Field002Chars00 ++ (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))))))) fragment0173580Acc00200 := object_fragment0173580_field_001 fuel (fragment0173580Field002Chars00 ++ (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 290) (SourceJson.white (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))))))) fragment0173580Acc00300 := object_fragment0173580_field_002 fuel (fragment0173580Field003Chars00 ++ (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 289) (SourceJson.white (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))))) fragment0173580Acc00400 := object_fragment0173580_field_003 fuel (fragment0173580Field004Chars00 ++ (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 288) (SourceJson.white (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))))) fragment0173580Acc00500 := object_fragment0173580_field_004 fuel (fragment0173580Field005Chars00 ++ (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 287) (SourceJson.white (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))) fragment0173580Acc00600 := object_fragment0173580_field_005 fuel (fragment0173580Field006Chars00 ++ (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 286) (SourceJson.white (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))) fragment0173580Acc00700 := object_fragment0173580_field_006 fuel (fragment0173580Field007Chars00 ++ (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 285) (SourceJson.white (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))) fragment0173580Acc00800 := object_fragment0173580_field_007 fuel (fragment0173580Field008Chars00 ++ (fragment0173580Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 284) (SourceJson.white (fragment0173580Field009Chars00 ++ (tail))) fragment0173580Acc00900 := object_fragment0173580_field_008 fuel (fragment0173580Field009Chars00 ++ (tail))
    _ = .ok (fragment0173580Value, tail) := object_fragment0173580_field_009 fuel (tail)

noncomputable def fragment0175302Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0175302Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0175302Field000Value00 : SourceJson := .number (String.ofList ['4', '1'])
noncomputable def fragment0175302Acc00100 : List (String × SourceJson) := (fragment0175302Field000Key00, fragment0175302Field000Value00) :: fragment0175302Acc00000
noncomputable def fragment0175302Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '1', ',']

theorem object_fragment0175302_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0175302Field000Chars00 ++ tail)) fragment0175302Acc00000 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0175302Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_000"
  err.flush

noncomputable def fragment0175302Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0175302Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0175302Acc00200 : List (String × SourceJson) := (fragment0175302Field001Key00, fragment0175302Field001Value00) :: fragment0175302Acc00100
noncomputable def fragment0175302Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0175302_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0175302Field001Chars00 ++ tail)) fragment0175302Acc00100 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0175302Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_001"
  err.flush

noncomputable def fragment0175302Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0175302Field002Value00 : SourceJson := .str (String.ofList ['5', '1', '4', '9', '1', '8', '4', '9', '7', '9', '6', '6', '5', '9', '3', '0', '4', '4', '0', '4', '9', '4', '9', '7', '8', '5', '0', '7', '6', '7', '3', '1', '8', '3', '/', '6', '6', '2', '3', '7', '1', '2', '0', '6', '4', '8', '1', '9', '3', '3', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0175302Acc00300 : List (String × SourceJson) := (fragment0175302Field002Key00, fragment0175302Field002Value00) :: fragment0175302Acc00200
noncomputable def fragment0175302Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '1', '4', '9', '1', '8', '4', '9', '7', '9', '6', '6', '5', '9', '3', '0', '4', '4', '0', '4', '9', '4', '9', '7', '8', '5', '0', '7', '6', '7', '3', '1', '8', '3', '/', '6', '6', '2', '3', '7', '1', '2', '0', '6', '4', '8', '1', '9', '3', '3', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0175302_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0175302Field002Chars00 ++ tail)) fragment0175302Acc00200 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0175302Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_002"
  err.flush

noncomputable def fragment0175302Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0175302Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0175302Acc00400 : List (String × SourceJson) := (fragment0175302Field003Key00, fragment0175302Field003Value00) :: fragment0175302Acc00300
noncomputable def fragment0175302Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0175302_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0175302Field003Chars00 ++ tail)) fragment0175302Acc00300 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0175302Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_003"
  err.flush

noncomputable def fragment0175302Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0175302Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0175302Acc00500 : List (String × SourceJson) := (fragment0175302Field004Key00, fragment0175302Field004Value00) :: fragment0175302Acc00400
noncomputable def fragment0175302Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0175302_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0175302Field004Chars00 ++ tail)) fragment0175302Acc00400 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0175302Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_004"
  err.flush

noncomputable def fragment0175302Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0175302Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '5', '9', '4', '1', '9', '0', '9', '8', '0', '5', '8', '4', '9', '/', '4', '1', '6', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '1', '9', '4', '3', '1', '0', '7', '3', '1', '2', '3', '/', '5', '2', '0', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '1', '4', '4', '5', '8', '2', '4', '1', '2', '5', '2', '9', '/', '2', '9', '1', '6', '5', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '5', '1', '3', '4', '8', '1', '9', '2', '9', '1', '6', '1', '/', '7', '2', '9', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '7', '2', '9', '4', '1', '6', '0', '0', '7', '1', '3', '9', '/', '7', '2', '9', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '4', '5', '8', '2', '3', '4', '4', '0', '9', '7', '/', '2', '9', '1', '6', '5', '4', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '8', '7', '8', '2', '7', '0', '3', '4', '0', '2', '2', '7', '/', '1', '4', '5', '8', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '9', '2', '8', '2', '5', '9', '3', '4', '3', '2', '3', '/', '6', '9', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '5', '0', '9', '7', '8', '0', '9', '8', '4', '3', '/', '6', '9', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '4', '2', '0', '9', '9', '5', '4', '8', '2', '7', '/', '1', '7', '3', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0175302Acc00600 : List (String × SourceJson) := (fragment0175302Field005Key00, fragment0175302Field005Value00) :: fragment0175302Acc00500
noncomputable def fragment0175302Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '4', '1', '9', '0', '9', '8', '0', '5', '8', '4', '9', '/', '4', '1', '6', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '1', '9', '4', '3', '1', '0', '7', '3', '1', '2', '3', '/', '5', '2', '0', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '4', '4', '5', '8', '2', '4', '1', '2', '5', '2', '9', '/', '2', '9', '1', '6', '5', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '5', '1', '3', '4', '8', '1', '9', '2', '9', '1', '6', '1', '/', '7', '2', '9', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '7', '2', '9', '4', '1', '6', '0', '0', '7', '1', '3', '9', '/', '7', '2', '9', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '4', '5', '8', '2', '3', '4', '4', '0', '9', '7', '/', '2', '9', '1', '6', '5', '4', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '8', '7', '8', '2', '7', '0', '3', '4', '0', '2', '2', '7', '/', '1', '4', '5', '8', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '9', '2', '8', '2', '5', '9', '3', '4', '3', '2', '3', '/', '6', '9', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '5', '0', '9', '7', '8', '0', '9', '8', '4', '3', '/', '6', '9', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '4', '2', '0', '9', '9', '5', '4', '8', '2', '7', '/', '1', '7', '3', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0175302_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0175302Field005Chars00 ++ tail)) fragment0175302Acc00500 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0175302Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_005"
  err.flush

noncomputable def fragment0175302Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0175302Field006Value00 : SourceJson := .str (String.ofList ['6', '7', '5', '2', '9', '1', '6', '6', '0', '7', '8', '4', '1', '5', '8', '3', '5', '1', '8', '7', '1', '3', '2', '0', '3', '1', '0', '0', '2', '6', '1', '9', '0', '0', '7', '4', '8', '2', '1', '8', '7', '1', '2', '5', '4', '1', '1', '0', '2', '0', '8', '0', '0', '0', '0', '/', '1', '4', '0', '2', '8', '7', '4', '9', '1', '3', '7', '6', '7', '1', '2', '8', '4', '4', '6', '9', '4', '3', '8', '6', '8', '8', '5', '3', '6', '5', '7', '2', '0', '0', '2', '4', '3', '1', '9', '2', '0', '8', '9', '1', '0', '4', '2', '9', '2', '5', '4', '2', '6', '6', '7', '0', '0', '5', '7', '9', '4', '1', '9', '8', '0', '5', '5', '0', '9'])
noncomputable def fragment0175302Acc00700 : List (String × SourceJson) := (fragment0175302Field006Key00, fragment0175302Field006Value00) :: fragment0175302Acc00600
noncomputable def fragment0175302Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '5', '2', '9', '1', '6', '6', '0', '7', '8', '4', '1', '5', '8', '3', '5', '1', '8', '7', '1', '3', '2', '0', '3', '1', '0', '0', '2', '6', '1', '9', '0', '0', '7', '4', '8', '2', '1', '8', '7', '1', '2', '5', '4', '1', '1', '0', '2', '0', '8', '0', '0', '0', '0', '/', '1', '4', '0', '2', '8', '7', '4', '9', '1', '3', '7', '6', '7', '1', '2', '8', '4', '4', '6', '9', '4', '3', '8', '6', '8', '8', '5', '3', '6', '5', '7', '2', '0', '0', '2', '4', '3', '1', '9', '2', '0', '8', '9', '1', '0', '4', '2', '9', '2', '5', '4', '2', '6', '6', '7', '0', '0', '5', '7', '9', '4', '1', '9', '8', '0', '5', '5', '0', '9', '"', ',']

theorem object_fragment0175302_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0175302Field006Chars00 ++ tail)) fragment0175302Acc00600 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0175302Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_006"
  err.flush

noncomputable def fragment0175302Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0175302Field007Value00 : SourceJson := .str (String.ofList ['3', '3', '2', '4', '9', '5', '5', '3', '8', '5', '8', '9', '6', '0', '6', '3', '6', '0', '3', '3', '6', '6', '4', '2', '1', '9', '8', '2', '3', '3', '5', '6', '4', '5', '0', '3', '5', '7', '1', '0', '7', '3', '5', '5', '7', '3', '3', '9', '5', '2', '2', '2', '8', '2', '5', '1', '2', '0', '6', '3', '4', '2', '5', '9', '2', '4', '9', '4', '0', '5', '2', '6', '3', '0', '5', '0', '9', '7', '3', '4', '8', '8', '5', '6', '6', '2', '9', '7', '9', '5', '2', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '2', '7', '7', '7', '2', '0', '9', '8', '1', '5', '9', '5', '0', '7', '6', '3', '2', '9', '0', '0', '5', '4', '9', '4', '5', '0', '8', '8', '7', '6', '4', '6', '7', '3', '4', '7', '5', '2', '0', '7', '7', '5', '8', '0', '5', '6', '1', '9', '1', '8', '9', '3', '2', '1', '1', '6', '9', '8', '3', '1', '9', '1', '2', '6', '7', '7', '4', '2', '9', '5', '8', '9', '1', '7', '6', '9', '9', '4', '1', '9', '1', '6', '5', '6', '7', '5', '4', '1', '8', '7', '7', '2', '3', '2', '4', '0', '4', '9', '7', '3', '5', '2', '6', '0', '9', '3', '1', '8', '4', '9', '5', '6', '2', '6', '8', '4', '1', '0', '2', '6', '6', '4', '6', '2', '7', '1'])
noncomputable def fragment0175302Acc00800 : List (String × SourceJson) := (fragment0175302Field007Key00, fragment0175302Field007Value00) :: fragment0175302Acc00700
noncomputable def fragment0175302Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '2', '4', '9', '5', '5', '3', '8', '5', '8', '9', '6', '0', '6', '3', '6', '0', '3', '3', '6', '6', '4', '2', '1', '9', '8', '2', '3', '3', '5', '6', '4', '5', '0', '3', '5', '7', '1', '0', '7', '3', '5', '5', '7', '3', '3', '9', '5', '2', '2', '2', '8', '2', '5', '1', '2', '0', '6', '3', '4', '2', '5', '9', '2', '4', '9', '4', '0', '5', '2', '6', '3', '0', '5', '0', '9', '7', '3', '4', '8', '8', '5', '6', '6', '2', '9', '7', '9', '5', '2', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '2', '7', '7', '7', '2', '0', '9', '8', '1', '5', '9', '5', '0', '7', '6', '3', '2', '9', '0', '0', '5', '4', '9', '4', '5', '0', '8', '8', '7', '6', '4', '6', '7', '3', '4', '7', '5', '2', '0', '7', '7', '5', '8', '0', '5', '6', '1', '9', '1', '8', '9', '3', '2', '1', '1', '6', '9', '8', '3', '1', '9', '1', '2', '6', '7', '7', '4', '2', '9', '5', '8', '9', '1', '7', '6', '9', '9', '4', '1', '9', '1', '6', '5', '6', '7', '5', '4', '1', '8', '7', '7', '2', '3', '2', '4', '0', '4', '9', '7', '3', '5', '2', '6', '0', '9', '3', '1', '8', '4', '9', '5', '6', '2', '6', '8', '4', '1', '0', '2', '6', '6', '4', '6', '2', '7', '1', '"', ',']

theorem object_fragment0175302_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0175302Field007Chars00 ++ tail)) fragment0175302Acc00700 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0175302Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_007"
  err.flush

noncomputable def fragment0175302Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0175302Field008Value00 : SourceJson := .str (String.ofList ['3', '8', '1', '3', '7', '4', '8', '2', '4', '7', '9', '7', '9', '2', '8', '4'])
noncomputable def fragment0175302Acc00900 : List (String × SourceJson) := (fragment0175302Field008Key00, fragment0175302Field008Value00) :: fragment0175302Acc00800
noncomputable def fragment0175302Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '8', '1', '3', '7', '4', '8', '2', '4', '7', '9', '7', '9', '2', '8', '4', '"', ',']

theorem object_fragment0175302_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0175302Field008Chars00 ++ tail)) fragment0175302Acc00800 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0175302Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_008"
  err.flush

noncomputable def fragment0175302Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0175302Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '1', '6', '8', '3', '4', '0', '6', '0', '9', '7', '7', '7', '6', '0'])
noncomputable def fragment0175302Acc01000 : List (String × SourceJson) := (fragment0175302Field009Key00, fragment0175302Field009Value00) :: fragment0175302Acc00900
noncomputable def fragment0175302Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '1', '6', '8', '3', '4', '0', '6', '0', '9', '7', '7', '7', '6', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0175302_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0175302Field009Chars00 ++ tail)) fragment0175302Acc00900 =
      .ok (.obj (fragment0175302Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0175302_object_field_009"
  err.flush

noncomputable def fragment0175302Chars : List Char := '{' :: (fragment0175302Field000Chars00 ++ fragment0175302Field001Chars00 ++ fragment0175302Field002Chars00 ++ fragment0175302Field003Chars00 ++ fragment0175302Field004Chars00 ++ fragment0175302Field005Chars00 ++ fragment0175302Field006Chars00 ++ fragment0175302Field007Chars00 ++ fragment0175302Field008Chars00 ++ fragment0175302Field009Chars00)
noncomputable def fragment0175302Value : SourceJson := .obj (fragment0175302Acc01000.reverse)

theorem value_fragment0175302 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 255) (fragment0175302Chars ++ tail) =
      .ok (fragment0175302Value, tail) := by
  have hinput : fragment0175302Chars ++ tail = '{' :: (fragment0175302Field000Chars00 ++ (fragment0175302Field001Chars00 ++ (fragment0175302Field002Chars00 ++ (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0175302Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 255) (fragment0175302Chars ++ tail) =
        SourceJson.value (fuel + 255) ('{' :: (fragment0175302Field000Chars00 ++ (fragment0175302Field001Chars00 ++ (fragment0175302Field002Chars00 ++ (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 255)) hinput
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0175302Field000Chars00 ++ (fragment0175302Field001Chars00 ++ (fragment0175302Field002Chars00 ++ (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))))))))) fragment0175302Acc00000 := by rfl
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0175302Field001Chars00 ++ (fragment0175302Field002Chars00 ++ (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))))))))) fragment0175302Acc00100 := object_fragment0175302_field_000 fuel (fragment0175302Field001Chars00 ++ (fragment0175302Field002Chars00 ++ (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0175302Field002Chars00 ++ (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))))))) fragment0175302Acc00200 := object_fragment0175302_field_001 fuel (fragment0175302Field002Chars00 ++ (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))))))) fragment0175302Acc00300 := object_fragment0175302_field_002 fuel (fragment0175302Field003Chars00 ++ (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))))) fragment0175302Acc00400 := object_fragment0175302_field_003 fuel (fragment0175302Field004Chars00 ++ (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))))) fragment0175302Acc00500 := object_fragment0175302_field_004 fuel (fragment0175302Field005Chars00 ++ (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))) fragment0175302Acc00600 := object_fragment0175302_field_005 fuel (fragment0175302Field006Chars00 ++ (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))) fragment0175302Acc00700 := object_fragment0175302_field_006 fuel (fragment0175302Field007Chars00 ++ (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))) fragment0175302Acc00800 := object_fragment0175302_field_007 fuel (fragment0175302Field008Chars00 ++ (fragment0175302Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0175302Field009Chars00 ++ (tail))) fragment0175302Acc00900 := object_fragment0175302_field_008 fuel (fragment0175302Field009Chars00 ++ (tail))
    _ = .ok (fragment0175302Value, tail) := object_fragment0175302_field_009 fuel (tail)

noncomputable def fragment0176947Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0176947Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0176947Field000Value00 : SourceJson := .number (String.ofList ['4', '2'])
noncomputable def fragment0176947Acc00100 : List (String × SourceJson) := (fragment0176947Field000Key00, fragment0176947Field000Value00) :: fragment0176947Acc00000
noncomputable def fragment0176947Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '2', ',']

theorem object_fragment0176947_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0176947Field000Chars00 ++ tail)) fragment0176947Acc00000 =
      SourceJson.object (fuel + 413) (SourceJson.white tail) fragment0176947Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_000"
  err.flush

noncomputable def fragment0176947Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0176947Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4'])]
noncomputable def fragment0176947Acc00200 : List (String × SourceJson) := (fragment0176947Field001Key00, fragment0176947Field001Value00) :: fragment0176947Acc00100
noncomputable def fragment0176947Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0176947_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 413) (SourceJson.white (fragment0176947Field001Chars00 ++ tail)) fragment0176947Acc00100 =
      SourceJson.object (fuel + 412) (SourceJson.white tail) fragment0176947Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_001"
  err.flush

noncomputable def fragment0176947Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0176947Field002Value00 : SourceJson := .str (String.ofList ['3', '2', '7', '0', '9', '8', '1', '3', '3', '1', '9', '1', '2', '0', '4', '4', '7', '3', '8', '5', '6', '2', '0', '7', '4', '1', '5', '8', '6', '6', '0', '2', '9', '3', '/', '7', '5', '4', '0', '3', '8', '6', '5', '0', '2', '3', '6', '1', '2', '9', '7', '6', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0176947Acc00300 : List (String × SourceJson) := (fragment0176947Field002Key00, fragment0176947Field002Value00) :: fragment0176947Acc00200
noncomputable def fragment0176947Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '2', '7', '0', '9', '8', '1', '3', '3', '1', '9', '1', '2', '0', '4', '4', '7', '3', '8', '5', '6', '2', '0', '7', '4', '1', '5', '8', '6', '6', '0', '2', '9', '3', '/', '7', '5', '4', '0', '3', '8', '6', '5', '0', '2', '3', '6', '1', '2', '9', '7', '6', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0176947_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 412) (SourceJson.white (fragment0176947Field002Chars00 ++ tail)) fragment0176947Acc00200 =
      SourceJson.object (fuel + 411) (SourceJson.white tail) fragment0176947Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_002"
  err.flush

noncomputable def fragment0176947Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0176947Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0176947Acc00400 : List (String × SourceJson) := (fragment0176947Field003Key00, fragment0176947Field003Value00) :: fragment0176947Acc00300
noncomputable def fragment0176947Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0176947_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 411) (SourceJson.white (fragment0176947Field003Chars00 ++ tail)) fragment0176947Acc00300 =
      SourceJson.object (fuel + 410) (SourceJson.white tail) fragment0176947Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_003"
  err.flush

noncomputable def fragment0176947Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0176947Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0176947Acc00500 : List (String × SourceJson) := (fragment0176947Field004Key00, fragment0176947Field004Value00) :: fragment0176947Acc00400
noncomputable def fragment0176947Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0176947_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 410) (SourceJson.white (fragment0176947Field004Chars00 ++ tail)) fragment0176947Acc00400 =
      SourceJson.object (fuel + 409) (SourceJson.white tail) fragment0176947Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_004"
  err.flush

noncomputable def fragment0176947Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0176947Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '8', '7', '3', '9', '8', '0', '0', '5', '3', '1', '6', '6', '8', '9', '6', '0', '6', '4', '7', '0', '7', '/', '1', '5', '1', '2', '8', '4', '3', '2', '7', '7', '2', '3', '4', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '4', '5', '8', '6', '1', '3', '6', '5', '7', '1', '0', '2', '6', '5', '2', '4', '9', '9', '/', '1', '1', '1', '2', '3', '8', '4', '7', '6', '2', '6', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '7', '7', '9', '2', '7', '3', '2', '8', '0', '3', '2', '7', '2', '4', '0', '0', '6', '5', '5', '3', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '6', '4', '4', '5', '2', '4', '6', '5', '5', '2', '9', '0', '4', '8', '7', '6', '2', '5', '9', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '2', '8', '7', '6', '2', '3', '3', '3', '6', '4', '1', '0', '4', '5', '7', '1', '5', '5', '3', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '6', '8', '2', '3', '1', '7', '9', '2', '5', '2', '1', '6', '5', '2', '2', '5', '1', '5', '7', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '6', '0', '7', '1', '0', '4', '6', '8', '5', '0', '0', '0', '5', '0', '6', '9', '2', '8', '7', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '1', '5', '5', '0', '1', '5', '8', '2', '0', '8', '6', '1', '3', '1', '7', '3', '4', '0', '1', '/', '2', '5', '2', '1', '4', '0', '5', '4', '6', '2', '0', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '9', '2', '8', '3', '7', '2', '6', '5', '4', '0', '9', '0', '4', '7', '9', '1', '0', '2', '7', '/', '8', '4', '0', '4', '6', '8', '4', '8', '7', '3', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '2', '1', '3', '0', '1', '5', '7', '6', '5', '0', '1', '3', '7', '8', '8', '5', '7', '/', '1', '2', '3', '5', '9', '8', '3', '0', '6', '9', '6', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0176947Acc00600 : List (String × SourceJson) := (fragment0176947Field005Key00, fragment0176947Field005Value00) :: fragment0176947Acc00500
noncomputable def fragment0176947Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '7', '3', '9', '8', '0', '0', '5', '3', '1', '6', '6', '8', '9', '6', '0', '6', '4', '7', '0', '7', '/', '1', '5', '1', '2', '8', '4', '3', '2', '7', '7', '2', '3', '4', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '4', '5', '8', '6', '1', '3', '6', '5', '7', '1', '0', '2', '6', '5', '2', '4', '9', '9', '/', '1', '1', '1', '2', '3', '8', '4', '7', '6', '2', '6', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '7', '7', '9', '2', '7', '3', '2', '8', '0', '3', '2', '7', '2', '4', '0', '0', '6', '5', '5', '3', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '6', '4', '4', '5', '2', '4', '6', '5', '5', '2', '9', '0', '4', '8', '7', '6', '2', '5', '9', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '2', '8', '7', '6', '2', '3', '3', '3', '6', '4', '1', '0', '4', '5', '7', '1', '5', '5', '3', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '6', '8', '2', '3', '1', '7', '9', '2', '5', '2', '1', '6', '5', '2', '2', '5', '1', '5', '7', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '6', '0', '7', '1', '0', '4', '6', '8', '5', '0', '0', '0', '5', '0', '6', '9', '2', '8', '7', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '1', '5', '5', '0', '1', '5', '8', '2', '0', '8', '6', '1', '3', '1', '7', '3', '4', '0', '1', '/', '2', '5', '2', '1', '4', '0', '5', '4', '6', '2', '0', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '2', '8', '3', '7', '2', '6', '5', '4', '0', '9', '0', '4', '7', '9', '1', '0', '2', '7', '/', '8', '4', '0', '4', '6', '8', '4', '8', '7', '3', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '2', '1', '3', '0', '1', '5', '7', '6', '5', '0', '1', '3', '7', '8', '8', '5', '7', '/', '1', '2', '3', '5', '9', '8', '3', '0', '6', '9', '6', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0176947_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0176947Field005Chars00 ++ tail)) fragment0176947Acc00500 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0176947Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_005"
  err.flush

noncomputable def fragment0176947Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0176947Field006Value00 : SourceJson := .str (String.ofList ['7', '6', '4', '1', '2', '2', '1', '1', '7', '4', '9', '6', '1', '8', '5', '9', '0', '8', '1', '9', '5', '4', '5', '8', '2', '1', '6', '8', '5', '1', '7', '7', '9', '4', '2', '3', '3', '5', '7', '9', '8', '1', '7', '4', '4', '2', '8', '8', '4', '3', '0', '5', '5', '5', '1', '3', '6', '0', '0', '/', '1', '1', '7', '8', '3', '4', '9', '0', '3', '5', '4', '2', '2', '5', '0', '1', '2', '0', '9', '8', '9', '7', '7', '1', '6', '4', '6', '3', '3', '7', '5', '1', '9', '2', '1', '9', '2', '0', '1', '2', '2', '8', '5', '2', '4', '8', '9', '3', '9', '2', '7', '0', '4', '5', '7', '0', '1', '2', '3', '8', '8', '3', '5', '1', '0', '2', '2', '8', '3', '6', '6', '4', '1'])
noncomputable def fragment0176947Acc00700 : List (String × SourceJson) := (fragment0176947Field006Key00, fragment0176947Field006Value00) :: fragment0176947Acc00600
noncomputable def fragment0176947Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '6', '4', '1', '2', '2', '1', '1', '7', '4', '9', '6', '1', '8', '5', '9', '0', '8', '1', '9', '5', '4', '5', '8', '2', '1', '6', '8', '5', '1', '7', '7', '9', '4', '2', '3', '3', '5', '7', '9', '8', '1', '7', '4', '4', '2', '8', '8', '4', '3', '0', '5', '5', '5', '1', '3', '6', '0', '0', '/', '1', '1', '7', '8', '3', '4', '9', '0', '3', '5', '4', '2', '2', '5', '0', '1', '2', '0', '9', '8', '9', '7', '7', '1', '6', '4', '6', '3', '3', '7', '5', '1', '9', '2', '1', '9', '2', '0', '1', '2', '2', '8', '5', '2', '4', '8', '9', '3', '9', '2', '7', '0', '4', '5', '7', '0', '1', '2', '3', '8', '8', '3', '5', '1', '0', '2', '2', '8', '3', '6', '6', '4', '1', '"', ',']

theorem object_fragment0176947_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0176947Field006Chars00 ++ tail)) fragment0176947Acc00600 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0176947Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_006"
  err.flush

noncomputable def fragment0176947Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0176947Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '0', '6', '3', '4', '1', '6', '2', '7', '8', '3', '4', '3', '6', '0', '8', '7', '2', '6', '2', '4', '0', '4', '8', '4', '1', '0', '1', '5', '9', '9', '1', '5', '2', '3', '6', '4', '0', '0', '1', '8', '2', '4', '8', '9', '8', '7', '0', '2', '9', '1', '2', '0', '2', '0', '0', '3', '1', '3', '6', '4', '5', '5', '2', '5', '4', '8', '2', '1', '7', '0', '0', '7', '5', '4', '7', '3', '4', '0', '7', '1', '1', '6', '3', '7', '0', '4', '6', '9', '4', '8', '8', '8', '8', '1', '5', '2', '6', '4', '6', '3', '3', '1', '9', '6', '4', '6', '5', '1', '1', '2', '1', '9', '4', '5', '6', '4', '7', '9', '6', '6', '4', '6', '0', '7', '6', '4', '9', '5', '2', '4', '5', '0', '7', '0', '7', '7', '1', '1', '9', '7', '5', '4', '4', '2', '3', '9', '0', '1', '8', '1', '6', '4', '2', '3', '4', '1', '2', '2', '3', '3', '9', '1', '3', '0', '3', '4', '0', '8', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '6', '2', '9', '6', '5', '3', '2', '3', '3', '9', '3', '9', '9', '7', '7', '8', '6', '8', '7', '9', '3', '8', '5', '4', '0', '9', '8', '1', '9', '4', '2', '6', '5', '9', '4', '2', '4', '2', '0', '0', '3', '6', '0', '4', '5', '9', '8', '4', '8', '8', '3', '4', '8', '4', '2', '4', '1', '0', '4', '0', '9', '4', '3', '6', '7', '7', '2', '8', '9', '8', '0', '0', '5', '3', '5', '6', '7', '9', '3', '9', '6', '7', '8', '6', '0', '0', '8', '4', '9', '8', '3', '4', '1', '2', '8', '1', '2', '0', '9', '0', '9', '6', '6', '7', '4', '1', '1', '0', '1', '8', '3', '7', '9', '9', '8', '8', '3', '5', '4', '0', '4', '5', '1', '3', '3', '9', '0', '3', '1', '3', '5', '8', '3', '9', '6', '8', '2', '5', '6', '4', '5', '9', '9', '1', '3', '3', '3', '3', '7', '3', '5', '1', '5', '5', '0', '0', '0', '9', '9', '2', '3', '4', '3', '6', '0', '5', '7', '1', '7', '0', '2', '4', '9', '8', '5', '4', '3', '6', '8', '5', '2', '0', '7', '8', '6', '2', '8', '8', '1', '6', '9', '6', '5', '2', '2', '3', '6', '8', '7', '9', '2', '9', '9', '6', '1'])
noncomputable def fragment0176947Acc00800 : List (String × SourceJson) := (fragment0176947Field007Key00, fragment0176947Field007Value00) :: fragment0176947Acc00700
noncomputable def fragment0176947Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '0', '6', '3', '4', '1', '6', '2', '7', '8', '3', '4', '3', '6', '0', '8', '7', '2', '6', '2', '4', '0', '4', '8', '4', '1', '0', '1', '5', '9', '9', '1', '5', '2', '3', '6', '4', '0', '0', '1', '8', '2', '4', '8', '9', '8', '7', '0', '2', '9', '1', '2', '0', '2', '0', '0', '3', '1', '3', '6', '4', '5', '5', '2', '5', '4', '8', '2', '1', '7', '0', '0', '7', '5', '4', '7', '3', '4', '0', '7', '1', '1', '6', '3', '7', '0', '4', '6', '9', '4', '8', '8', '8', '8', '1', '5', '2', '6', '4', '6', '3', '3', '1', '9', '6', '4', '6', '5', '1', '1', '2', '1', '9', '4', '5', '6', '4', '7', '9', '6', '6', '4', '6', '0', '7', '6', '4', '9', '5', '2', '4', '5', '0', '7', '0', '7', '7', '1', '1', '9', '7', '5', '4', '4', '2', '3', '9', '0', '1', '8', '1', '6', '4', '2', '3', '4', '1', '2', '2', '3', '3', '9', '1', '3', '0', '3', '4', '0', '8', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '6', '2', '9', '6', '5', '3', '2', '3', '3', '9', '3', '9', '9', '7', '7', '8', '6', '8', '7', '9', '3', '8', '5', '4', '0', '9', '8', '1', '9', '4', '2', '6', '5', '9', '4', '2', '4', '2', '0', '0', '3', '6', '0', '4', '5', '9', '8', '4', '8', '8', '3', '4', '8', '4', '2', '4', '1', '0', '4', '0', '9', '4', '3', '6', '7', '7', '2', '8', '9', '8', '0', '0', '5', '3', '5', '6', '7', '9', '3', '9', '6', '7', '8', '6', '0', '0', '8', '4', '9', '8', '3', '4', '1', '2', '8', '1', '2', '0', '9', '0', '9', '6', '6', '7', '4', '1', '1', '0', '1', '8', '3', '7', '9', '9', '8', '8', '3', '5', '4', '0', '4', '5', '1', '3', '3', '9', '0', '3', '1', '3', '5', '8', '3', '9', '6', '8', '2', '5', '6', '4', '5', '9', '9', '1', '3', '3', '3', '3', '7', '3', '5', '1', '5', '5', '0', '0', '0', '9', '9', '2', '3', '4', '3', '6', '0', '5', '7', '1', '7', '0', '2', '4', '9', '8', '5', '4', '3', '6', '8', '5', '2', '0', '7', '8', '6', '2', '8', '8', '1', '6', '9', '6', '5', '2', '2', '3', '6', '8', '7', '9', '2', '9', '9', '6', '1', '"', ',']

theorem object_fragment0176947_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0176947Field007Chars00 ++ tail)) fragment0176947Acc00700 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0176947Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_007"
  err.flush

noncomputable def fragment0176947Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0176947Field008Value00 : SourceJson := .str (String.ofList ['5', '1', '3', '7', '6', '9', '6', '0', '0', '3', '9', '7', '0', '9', '0', '9'])
noncomputable def fragment0176947Acc00900 : List (String × SourceJson) := (fragment0176947Field008Key00, fragment0176947Field008Value00) :: fragment0176947Acc00800
noncomputable def fragment0176947Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '3', '7', '6', '9', '6', '0', '0', '3', '9', '7', '0', '9', '0', '9', '"', ',']

theorem object_fragment0176947_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0176947Field008Chars00 ++ tail)) fragment0176947Acc00800 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0176947Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_008"
  err.flush

noncomputable def fragment0176947Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0176947Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '6', '0', '6', '9', '3', '7', '9', '8', '8', '6', '1', '3', '8', '4'])
noncomputable def fragment0176947Acc01000 : List (String × SourceJson) := (fragment0176947Field009Key00, fragment0176947Field009Value00) :: fragment0176947Acc00900
noncomputable def fragment0176947Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '6', '0', '6', '9', '3', '7', '9', '8', '8', '6', '1', '3', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0176947_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0176947Field009Chars00 ++ tail)) fragment0176947Acc00900 =
      .ok (.obj (fragment0176947Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176947_object_field_009"
  err.flush

noncomputable def fragment0176947Chars : List Char := '{' :: (fragment0176947Field000Chars00 ++ fragment0176947Field001Chars00 ++ fragment0176947Field002Chars00 ++ fragment0176947Field003Chars00 ++ fragment0176947Field004Chars00 ++ fragment0176947Field005Chars00 ++ fragment0176947Field006Chars00 ++ fragment0176947Field007Chars00 ++ fragment0176947Field008Chars00 ++ fragment0176947Field009Chars00)
noncomputable def fragment0176947Value : SourceJson := .obj (fragment0176947Acc01000.reverse)

theorem value_fragment0176947 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 415) (fragment0176947Chars ++ tail) =
      .ok (fragment0176947Value, tail) := by
  have hinput : fragment0176947Chars ++ tail = '{' :: (fragment0176947Field000Chars00 ++ (fragment0176947Field001Chars00 ++ (fragment0176947Field002Chars00 ++ (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0176947Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 415) (fragment0176947Chars ++ tail) =
        SourceJson.value (fuel + 415) ('{' :: (fragment0176947Field000Chars00 ++ (fragment0176947Field001Chars00 ++ (fragment0176947Field002Chars00 ++ (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 415)) hinput
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0176947Field000Chars00 ++ (fragment0176947Field001Chars00 ++ (fragment0176947Field002Chars00 ++ (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))))))))) fragment0176947Acc00000 := by rfl
    _ = SourceJson.object (fuel + 413) (SourceJson.white (fragment0176947Field001Chars00 ++ (fragment0176947Field002Chars00 ++ (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))))))))) fragment0176947Acc00100 := object_fragment0176947_field_000 fuel (fragment0176947Field001Chars00 ++ (fragment0176947Field002Chars00 ++ (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 412) (SourceJson.white (fragment0176947Field002Chars00 ++ (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))))))) fragment0176947Acc00200 := object_fragment0176947_field_001 fuel (fragment0176947Field002Chars00 ++ (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 411) (SourceJson.white (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))))))) fragment0176947Acc00300 := object_fragment0176947_field_002 fuel (fragment0176947Field003Chars00 ++ (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 410) (SourceJson.white (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))))) fragment0176947Acc00400 := object_fragment0176947_field_003 fuel (fragment0176947Field004Chars00 ++ (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))))) fragment0176947Acc00500 := object_fragment0176947_field_004 fuel (fragment0176947Field005Chars00 ++ (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))) fragment0176947Acc00600 := object_fragment0176947_field_005 fuel (fragment0176947Field006Chars00 ++ (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))) fragment0176947Acc00700 := object_fragment0176947_field_006 fuel (fragment0176947Field007Chars00 ++ (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))) fragment0176947Acc00800 := object_fragment0176947_field_007 fuel (fragment0176947Field008Chars00 ++ (fragment0176947Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0176947Field009Chars00 ++ (tail))) fragment0176947Acc00900 := object_fragment0176947_field_008 fuel (fragment0176947Field009Chars00 ++ (tail))
    _ = .ok (fragment0176947Value, tail) := object_fragment0176947_field_009 fuel (tail)

noncomputable def fragment0178918Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0178918Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0178918Field000Value00 : SourceJson := .number (String.ofList ['4', '3'])
noncomputable def fragment0178918Acc00100 : List (String × SourceJson) := (fragment0178918Field000Key00, fragment0178918Field000Value00) :: fragment0178918Acc00000
noncomputable def fragment0178918Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '3', ',']

theorem object_fragment0178918_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0178918Field000Chars00 ++ tail)) fragment0178918Acc00000 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0178918Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_000"
  err.flush

noncomputable def fragment0178918Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0178918Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0178918Acc00200 : List (String × SourceJson) := (fragment0178918Field001Key00, fragment0178918Field001Value00) :: fragment0178918Acc00100
noncomputable def fragment0178918Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0178918_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0178918Field001Chars00 ++ tail)) fragment0178918Acc00100 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0178918Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_001"
  err.flush

noncomputable def fragment0178918Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0178918Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '1', '0', '5', '1', '6', '8', '9', '9', '3', '1', '3', '7', '9', '7', '4', '0', '6', '2', '4', '0', '8', '0', '0', '1', '2', '8', '3', '8', '6', '3', '5', '6', '6', '6', '7', '/', '2', '9', '4', '9', '5', '6', '9', '0', '8', '9', '0', '4', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0178918Acc00300 : List (String × SourceJson) := (fragment0178918Field002Key00, fragment0178918Field002Value00) :: fragment0178918Acc00200
noncomputable def fragment0178918Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '1', '0', '5', '1', '6', '8', '9', '9', '3', '1', '3', '7', '9', '7', '4', '0', '6', '2', '4', '0', '8', '0', '0', '1', '2', '8', '3', '8', '6', '3', '5', '6', '6', '6', '7', '/', '2', '9', '4', '9', '5', '6', '9', '0', '8', '9', '0', '4', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0178918_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0178918Field002Chars00 ++ tail)) fragment0178918Acc00200 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0178918Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_002"
  err.flush

noncomputable def fragment0178918Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0178918Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0178918Acc00400 : List (String × SourceJson) := (fragment0178918Field003Key00, fragment0178918Field003Value00) :: fragment0178918Acc00300
noncomputable def fragment0178918Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0178918_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0178918Field003Chars00 ++ tail)) fragment0178918Acc00300 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0178918Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_003"
  err.flush

noncomputable def fragment0178918Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0178918Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0178918Acc00500 : List (String × SourceJson) := (fragment0178918Field004Key00, fragment0178918Field004Value00) :: fragment0178918Acc00400
noncomputable def fragment0178918Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0178918_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0178918Field004Chars00 ++ tail)) fragment0178918Acc00400 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0178918Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_004"
  err.flush

noncomputable def fragment0178918Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0178918Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '7', '6', '6', '0', '6', '7', '6', '1', '0', '0', '6', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '9', '1', '2', '7', '7', '7', '6', '6', '9', '2', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '5', '0', '1', '2', '7', '6', '2', '0', '4', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '4', '0', '2', '6', '4', '5', '5', '3', '3', '3', '/', '4', '3', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '4', '2', '9', '6', '4', '8', '5', '4', '1', '1', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '3', '6', '6', '5', '7', '0', '6', '7', '1', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '7', '0', '6', '9', '9', '0', '3', '5', '1', '/', '8', '7', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '4', '2', '8', '1', '3', '0', '5', '0', '0', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '7', '2', '7', '8', '1', '5', '8', '2', '0', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '7', '2', '7', '1', '1', '8', '9', '5', '6', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0178918Acc00600 : List (String × SourceJson) := (fragment0178918Field005Key00, fragment0178918Field005Value00) :: fragment0178918Acc00500
noncomputable def fragment0178918Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '6', '6', '0', '6', '7', '6', '1', '0', '0', '6', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '9', '1', '2', '7', '7', '7', '6', '6', '9', '2', '7', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '5', '0', '1', '2', '7', '6', '2', '0', '4', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '4', '0', '2', '6', '4', '5', '5', '3', '3', '3', '/', '4', '3', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '4', '2', '9', '6', '4', '8', '5', '4', '1', '1', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '3', '6', '6', '5', '7', '0', '6', '7', '1', '9', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '7', '0', '6', '9', '9', '0', '3', '5', '1', '/', '8', '7', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '4', '2', '8', '1', '3', '0', '5', '0', '0', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '7', '2', '7', '8', '1', '5', '8', '2', '0', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '7', '2', '7', '1', '1', '8', '9', '5', '6', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0178918_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0178918Field005Chars00 ++ tail)) fragment0178918Acc00500 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0178918Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_005"
  err.flush

noncomputable def fragment0178918Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0178918Field006Value00 : SourceJson := .str (String.ofList ['1', '7', '0', '9', '0', '5', '4', '7', '5', '3', '4', '9', '1', '8', '2', '4', '8', '6', '3', '0', '4', '4', '3', '8', '8', '6', '8', '2', '9', '1', '0', '8', '5', '3', '3', '7', '3', '1', '3', '2', '6', '6', '7', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '7', '8', '5', '0', '3', '6', '9', '7', '2', '2', '9', '5', '9', '7', '0', '2', '1', '5', '2', '8', '5', '5', '8', '9', '3', '3', '9', '3', '3', '6', '7', '3', '0', '9', '1', '5', '7', '2', '8', '3', '2', '7', '2', '7', '4', '9', '6', '1', '4', '1', '7', '6', '7', '0', '3', '4', '9', '8', '5', '2', '7', '5', '8', '1'])
noncomputable def fragment0178918Acc00700 : List (String × SourceJson) := (fragment0178918Field006Key00, fragment0178918Field006Value00) :: fragment0178918Acc00600
noncomputable def fragment0178918Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '0', '9', '0', '5', '4', '7', '5', '3', '4', '9', '1', '8', '2', '4', '8', '6', '3', '0', '4', '4', '3', '8', '8', '6', '8', '2', '9', '1', '0', '8', '5', '3', '3', '7', '3', '1', '3', '2', '6', '6', '7', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '7', '8', '5', '0', '3', '6', '9', '7', '2', '2', '9', '5', '9', '7', '0', '2', '1', '5', '2', '8', '5', '5', '8', '9', '3', '3', '9', '3', '3', '6', '7', '3', '0', '9', '1', '5', '7', '2', '8', '3', '2', '7', '2', '7', '4', '9', '6', '1', '4', '1', '7', '6', '7', '0', '3', '4', '9', '8', '5', '2', '7', '5', '8', '1', '"', ',']

theorem object_fragment0178918_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0178918Field006Chars00 ++ tail)) fragment0178918Acc00600 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0178918Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_006"
  err.flush

noncomputable def fragment0178918Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0178918Field007Value00 : SourceJson := .str (String.ofList ['7', '9', '9', '9', '5', '6', '5', '6', '0', '3', '7', '9', '6', '7', '2', '0', '7', '0', '9', '9', '2', '3', '2', '0', '5', '6', '2', '5', '7', '7', '9', '5', '7', '4', '3', '7', '9', '0', '1', '4', '1', '1', '0', '3', '0', '1', '4', '1', '1', '8', '5', '7', '1', '0', '6', '1', '9', '5', '2', '6', '8', '8', '6', '4', '1', '4', '9', '4', '9', '0', '3', '0', '5', '3', '7', '0', '5', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '5', '9', '3', '3', '1', '5', '8', '4', '9', '4', '2', '7', '7', '7', '1', '7', '1', '9', '3', '3', '1', '1', '5', '8', '8', '1', '9', '9', '2', '3', '7', '9', '5', '8', '1', '8', '3', '1', '5', '6', '7', '5', '2', '0', '3', '2', '0', '7', '3', '4', '4', '2', '3', '2', '2', '6', '5', '5', '1', '2', '8', '6', '2', '0', '3', '3', '2', '5', '4', '2', '6', '9', '0', '2', '9', '0', '6', '3', '6', '1', '4', '2', '6', '9', '2', '8', '2', '9', '8', '5', '8', '5', '2', '6', '5', '9', '5', '9', '3', '9', '2', '5', '1', '8', '8', '5', '3', '4', '5', '6', '2', '8', '9', '6', '5', '6', '1', '0', '0', '1'])
noncomputable def fragment0178918Acc00800 : List (String × SourceJson) := (fragment0178918Field007Key00, fragment0178918Field007Value00) :: fragment0178918Acc00700
noncomputable def fragment0178918Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '9', '9', '9', '5', '6', '5', '6', '0', '3', '7', '9', '6', '7', '2', '0', '7', '0', '9', '9', '2', '3', '2', '0', '5', '6', '2', '5', '7', '7', '9', '5', '7', '4', '3', '7', '9', '0', '1', '4', '1', '1', '0', '3', '0', '1', '4', '1', '1', '8', '5', '7', '1', '0', '6', '1', '9', '5', '2', '6', '8', '8', '6', '4', '1', '4', '9', '4', '9', '0', '3', '0', '5', '3', '7', '0', '5', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '5', '9', '3', '3', '1', '5', '8', '4', '9', '4', '2', '7', '7', '7', '1', '7', '1', '9', '3', '3', '1', '1', '5', '8', '8', '1', '9', '9', '2', '3', '7', '9', '5', '8', '1', '8', '3', '1', '5', '6', '7', '5', '2', '0', '3', '2', '0', '7', '3', '4', '4', '2', '3', '2', '2', '6', '5', '5', '1', '2', '8', '6', '2', '0', '3', '3', '2', '5', '4', '2', '6', '9', '0', '2', '9', '0', '6', '3', '6', '1', '4', '2', '6', '9', '2', '8', '2', '9', '8', '5', '8', '5', '2', '6', '5', '9', '5', '9', '3', '9', '2', '5', '1', '8', '8', '5', '3', '4', '5', '6', '2', '8', '9', '6', '5', '6', '1', '0', '0', '1', '"', ',']

theorem object_fragment0178918_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0178918Field007Chars00 ++ tail)) fragment0178918Acc00700 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0178918Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_007"
  err.flush

noncomputable def fragment0178918Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0178918Field008Value00 : SourceJson := .str (String.ofList ['4', '3', '5', '6', '8', '7', '8', '6', '0', '2', '4', '7'])
noncomputable def fragment0178918Acc00900 : List (String × SourceJson) := (fragment0178918Field008Key00, fragment0178918Field008Value00) :: fragment0178918Acc00800
noncomputable def fragment0178918Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '5', '6', '8', '7', '8', '6', '0', '2', '4', '7', '"', ',']

theorem object_fragment0178918_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0178918Field008Chars00 ++ tail)) fragment0178918Acc00800 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0178918Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_008"
  err.flush

noncomputable def fragment0178918Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0178918Field009Value00 : SourceJson := .str (String.ofList ['1', '8', '8', '6', '6', '5', '7', '7', '1', '0', '5', '4', '5'])
noncomputable def fragment0178918Acc01000 : List (String × SourceJson) := (fragment0178918Field009Key00, fragment0178918Field009Value00) :: fragment0178918Acc00900
noncomputable def fragment0178918Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '8', '6', '6', '5', '7', '7', '1', '0', '5', '4', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0178918_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0178918Field009Chars00 ++ tail)) fragment0178918Acc00900 =
      .ok (.obj (fragment0178918Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178918_object_field_009"
  err.flush

noncomputable def fragment0178918Chars : List Char := '{' :: (fragment0178918Field000Chars00 ++ fragment0178918Field001Chars00 ++ fragment0178918Field002Chars00 ++ fragment0178918Field003Chars00 ++ fragment0178918Field004Chars00 ++ fragment0178918Field005Chars00 ++ fragment0178918Field006Chars00 ++ fragment0178918Field007Chars00 ++ fragment0178918Field008Chars00 ++ fragment0178918Field009Chars00)
noncomputable def fragment0178918Value : SourceJson := .obj (fragment0178918Acc01000.reverse)

theorem value_fragment0178918 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 239) (fragment0178918Chars ++ tail) =
      .ok (fragment0178918Value, tail) := by
  have hinput : fragment0178918Chars ++ tail = '{' :: (fragment0178918Field000Chars00 ++ (fragment0178918Field001Chars00 ++ (fragment0178918Field002Chars00 ++ (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0178918Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 239) (fragment0178918Chars ++ tail) =
        SourceJson.value (fuel + 239) ('{' :: (fragment0178918Field000Chars00 ++ (fragment0178918Field001Chars00 ++ (fragment0178918Field002Chars00 ++ (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 239)) hinput
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0178918Field000Chars00 ++ (fragment0178918Field001Chars00 ++ (fragment0178918Field002Chars00 ++ (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))))))))) fragment0178918Acc00000 := by rfl
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0178918Field001Chars00 ++ (fragment0178918Field002Chars00 ++ (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))))))))) fragment0178918Acc00100 := object_fragment0178918_field_000 fuel (fragment0178918Field001Chars00 ++ (fragment0178918Field002Chars00 ++ (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0178918Field002Chars00 ++ (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))))))) fragment0178918Acc00200 := object_fragment0178918_field_001 fuel (fragment0178918Field002Chars00 ++ (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))))))) fragment0178918Acc00300 := object_fragment0178918_field_002 fuel (fragment0178918Field003Chars00 ++ (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))))) fragment0178918Acc00400 := object_fragment0178918_field_003 fuel (fragment0178918Field004Chars00 ++ (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))))) fragment0178918Acc00500 := object_fragment0178918_field_004 fuel (fragment0178918Field005Chars00 ++ (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))) fragment0178918Acc00600 := object_fragment0178918_field_005 fuel (fragment0178918Field006Chars00 ++ (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))) fragment0178918Acc00700 := object_fragment0178918_field_006 fuel (fragment0178918Field007Chars00 ++ (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))) fragment0178918Acc00800 := object_fragment0178918_field_007 fuel (fragment0178918Field008Chars00 ++ (fragment0178918Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0178918Field009Chars00 ++ (tail))) fragment0178918Acc00900 := object_fragment0178918_field_008 fuel (fragment0178918Field009Chars00 ++ (tail))
    _ = .ok (fragment0178918Value, tail) := object_fragment0178918_field_009 fuel (tail)

noncomputable def fragment0180516Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0180516Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0180516Field000Value00 : SourceJson := .number (String.ofList ['4', '4'])
noncomputable def fragment0180516Acc00100 : List (String × SourceJson) := (fragment0180516Field000Key00, fragment0180516Field000Value00) :: fragment0180516Acc00000
noncomputable def fragment0180516Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '4', ',']

theorem object_fragment0180516_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0180516Field000Chars00 ++ tail)) fragment0180516Acc00000 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0180516Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_000"
  err.flush

noncomputable def fragment0180516Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0180516Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0180516Acc00200 : List (String × SourceJson) := (fragment0180516Field001Key00, fragment0180516Field001Value00) :: fragment0180516Acc00100
noncomputable def fragment0180516Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0180516_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0180516Field001Chars00 ++ tail)) fragment0180516Acc00100 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0180516Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_001"
  err.flush

noncomputable def fragment0180516Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0180516Field002Value00 : SourceJson := .str (String.ofList ['4', '6', '7', '8', '7', '4', '2', '1', '0', '5', '4', '7', '7', '8', '5', '1', '7', '4', '2', '2', '8', '8', '9', '6', '9', '2', '9', '6', '5', '9', '9', '8', '1', '7', '9', '1', '/', '4', '0', '3', '8', '1', '0', '0', '5', '3', '8', '5', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0180516Acc00300 : List (String × SourceJson) := (fragment0180516Field002Key00, fragment0180516Field002Value00) :: fragment0180516Acc00200
noncomputable def fragment0180516Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '6', '7', '8', '7', '4', '2', '1', '0', '5', '4', '7', '7', '8', '5', '1', '7', '4', '2', '2', '8', '8', '9', '6', '9', '2', '9', '6', '5', '9', '9', '8', '1', '7', '9', '1', '/', '4', '0', '3', '8', '1', '0', '0', '5', '3', '8', '5', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0180516_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0180516Field002Chars00 ++ tail)) fragment0180516Acc00200 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0180516Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_002"
  err.flush

noncomputable def fragment0180516Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0180516Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0180516Acc00400 : List (String × SourceJson) := (fragment0180516Field003Key00, fragment0180516Field003Value00) :: fragment0180516Acc00300
noncomputable def fragment0180516Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0180516_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0180516Field003Chars00 ++ tail)) fragment0180516Acc00300 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0180516Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_003"
  err.flush

noncomputable def fragment0180516Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0180516Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0180516Acc00500 : List (String × SourceJson) := (fragment0180516Field004Key00, fragment0180516Field004Value00) :: fragment0180516Acc00400
noncomputable def fragment0180516Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0180516_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0180516Field004Chars00 ++ tail)) fragment0180516Acc00400 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0180516Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_004"
  err.flush

noncomputable def fragment0180516Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0180516Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '8', '9', '2', '5', '3', '2', '6', '0', '4', '8', '5', '4', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '5', '0', '5', '1', '5', '9', '6', '5', '6', '3', '2', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '1', '3', '4', '7', '4', '4', '1', '8', '0', '8', '7', '9', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '0', '9', '2', '3', '8', '9', '7', '0', '2', '8', '9', '/', '1', '6', '6', '9', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '2', '0', '9', '0', '7', '1', '5', '4', '7', '8', '7', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '4', '9', '7', '2', '1', '2', '0', '1', '5', '7', '/', '4', '8', '0', '8', '3', '6', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '3', '1', '9', '8', '9', '6', '7', '2', '3', '4', '3', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '2', '3', '1', '6', '5', '6', '6', '9', '7', '9', '7', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '1', '7', '0', '7', '4', '6', '7', '1', '8', '6', '6', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '1', '7', '0', '5', '8', '6', '4', '3', '9', '9', '4', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0180516Acc00600 : List (String × SourceJson) := (fragment0180516Field005Key00, fragment0180516Field005Value00) :: fragment0180516Acc00500
noncomputable def fragment0180516Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '9', '2', '5', '3', '2', '6', '0', '4', '8', '5', '4', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '5', '0', '5', '1', '5', '9', '6', '5', '6', '3', '2', '1', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '3', '4', '7', '4', '4', '1', '8', '0', '8', '7', '9', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '9', '2', '3', '8', '9', '7', '0', '2', '8', '9', '/', '1', '6', '6', '9', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '2', '0', '9', '0', '7', '1', '5', '4', '7', '8', '7', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '4', '9', '7', '2', '1', '2', '0', '1', '5', '7', '/', '4', '8', '0', '8', '3', '6', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '3', '1', '9', '8', '9', '6', '7', '2', '3', '4', '3', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '3', '1', '6', '5', '6', '6', '9', '7', '9', '7', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '1', '7', '0', '7', '4', '6', '7', '1', '8', '6', '6', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '1', '7', '0', '5', '8', '6', '4', '3', '9', '9', '4', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0180516_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0180516Field005Chars00 ++ tail)) fragment0180516Acc00500 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0180516Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_005"
  err.flush

noncomputable def fragment0180516Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0180516Field006Value00 : SourceJson := .str (String.ofList ['5', '3', '5', '7', '2', '6', '1', '1', '1', '1', '8', '7', '3', '7', '7', '1', '6', '9', '2', '1', '8', '0', '4', '4', '8', '1', '8', '0', '0', '8', '6', '8', '1', '9', '6', '3', '3', '9', '1', '2', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '5', '9', '0', '4', '9', '4', '2', '6', '0', '1', '3', '8', '7', '9', '7', '5', '1', '7', '3', '5', '4', '3', '9', '1', '4', '6', '1', '4', '8', '1', '9', '2', '0', '1', '2', '7', '5', '6', '9', '6', '3', '9', '3', '3', '3', '3', '1', '7', '5', '0', '5', '2', '3', '8', '1', '6', '9', '8', '5', '8', '4', '9', '3', '2', '3', '9'])
noncomputable def fragment0180516Acc00700 : List (String × SourceJson) := (fragment0180516Field006Key00, fragment0180516Field006Value00) :: fragment0180516Acc00600
noncomputable def fragment0180516Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '3', '5', '7', '2', '6', '1', '1', '1', '1', '8', '7', '3', '7', '7', '1', '6', '9', '2', '1', '8', '0', '4', '4', '8', '1', '8', '0', '0', '8', '6', '8', '1', '9', '6', '3', '3', '9', '1', '2', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '5', '9', '0', '4', '9', '4', '2', '6', '0', '1', '3', '8', '7', '9', '7', '5', '1', '7', '3', '5', '4', '3', '9', '1', '4', '6', '1', '4', '8', '1', '9', '2', '0', '1', '2', '7', '5', '6', '9', '6', '3', '9', '3', '3', '3', '3', '1', '7', '5', '0', '5', '2', '3', '8', '1', '6', '9', '8', '5', '8', '4', '9', '3', '2', '3', '9', '"', ',']

theorem object_fragment0180516_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0180516Field006Chars00 ++ tail)) fragment0180516Acc00600 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0180516Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_006"
  err.flush

noncomputable def fragment0180516Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0180516Field007Value00 : SourceJson := .str (String.ofList ['7', '3', '1', '8', '4', '3', '2', '2', '9', '6', '3', '5', '1', '7', '5', '7', '4', '0', '6', '5', '2', '4', '5', '4', '7', '9', '2', '7', '8', '9', '9', '4', '1', '9', '4', '1', '1', '3', '5', '1', '1', '2', '8', '6', '6', '0', '5', '9', '9', '1', '5', '5', '1', '2', '6', '0', '3', '4', '4', '1', '9', '0', '9', '7', '2', '7', '2', '7', '9', '3', '7', '5', '9', '2', '5', '0', '1', '9', '2', '8', '5', '4', '3', '6', '1', '7', '9', '0', '8', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '5', '3', '2', '7', '6', '7', '7', '8', '2', '4', '1', '8', '6', '5', '0', '2', '1', '9', '3', '7', '1', '3', '4', '7', '0', '5', '9', '5', '4', '3', '3', '6', '5', '4', '0', '4', '1', '3', '6', '7', '0', '7', '4', '5', '3', '2', '1', '5', '1', '1', '3', '4', '2', '7', '3', '0', '6', '3', '2', '5', '3', '1', '1', '0', '8', '9', '2', '4', '8', '6', '9', '6', '3', '8', '9', '7', '3', '7', '6', '3', '5', '2', '0', '7', '0', '4', '5', '2', '9', '5', '4', '9', '5', '9', '1', '1', '6', '4', '8', '4', '1', '8', '5', '1', '0', '7', '7', '2', '4', '1', '9', '5', '4', '9', '8', '0', '0', '9', '0', '6', '0', '3', '6', '1', '8', '8', '7', '9', '9', '7'])
noncomputable def fragment0180516Acc00800 : List (String × SourceJson) := (fragment0180516Field007Key00, fragment0180516Field007Value00) :: fragment0180516Acc00700
noncomputable def fragment0180516Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '3', '1', '8', '4', '3', '2', '2', '9', '6', '3', '5', '1', '7', '5', '7', '4', '0', '6', '5', '2', '4', '5', '4', '7', '9', '2', '7', '8', '9', '9', '4', '1', '9', '4', '1', '1', '3', '5', '1', '1', '2', '8', '6', '6', '0', '5', '9', '9', '1', '5', '5', '1', '2', '6', '0', '3', '4', '4', '1', '9', '0', '9', '7', '2', '7', '2', '7', '9', '3', '7', '5', '9', '2', '5', '0', '1', '9', '2', '8', '5', '4', '3', '6', '1', '7', '9', '0', '8', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '5', '3', '2', '7', '6', '7', '7', '8', '2', '4', '1', '8', '6', '5', '0', '2', '1', '9', '3', '7', '1', '3', '4', '7', '0', '5', '9', '5', '4', '3', '3', '6', '5', '4', '0', '4', '1', '3', '6', '7', '0', '7', '4', '5', '3', '2', '1', '5', '1', '1', '3', '4', '2', '7', '3', '0', '6', '3', '2', '5', '3', '1', '1', '0', '8', '9', '2', '4', '8', '6', '9', '6', '3', '8', '9', '7', '3', '7', '6', '3', '5', '2', '0', '7', '0', '4', '5', '2', '9', '5', '4', '9', '5', '9', '1', '1', '6', '4', '8', '4', '1', '8', '5', '1', '0', '7', '7', '2', '4', '1', '9', '5', '4', '9', '8', '0', '0', '9', '0', '6', '0', '3', '6', '1', '8', '8', '7', '9', '9', '7', '"', ',']

theorem object_fragment0180516_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0180516Field007Chars00 ++ tail)) fragment0180516Acc00700 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0180516Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_007"
  err.flush

noncomputable def fragment0180516Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0180516Field008Value00 : SourceJson := .str (String.ofList ['3', '6', '6', '2', '0', '1', '7', '7', '2', '3', '1', '1'])
noncomputable def fragment0180516Acc00900 : List (String × SourceJson) := (fragment0180516Field008Key00, fragment0180516Field008Value00) :: fragment0180516Acc00800
noncomputable def fragment0180516Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '6', '2', '0', '1', '7', '7', '2', '3', '1', '1', '"', ',']

theorem object_fragment0180516_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0180516Field008Chars00 ++ tail)) fragment0180516Acc00800 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0180516Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_008"
  err.flush

noncomputable def fragment0180516Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0180516Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '1', '9', '2', '9', '8', '8', '3', '7', '6', '7'])
noncomputable def fragment0180516Acc01000 : List (String × SourceJson) := (fragment0180516Field009Key00, fragment0180516Field009Value00) :: fragment0180516Acc00900
noncomputable def fragment0180516Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '1', '9', '2', '9', '8', '8', '3', '7', '6', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0180516_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0180516Field009Chars00 ++ tail)) fragment0180516Acc00900 =
      .ok (.obj (fragment0180516Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180516_object_field_009"
  err.flush

noncomputable def fragment0180516Chars : List Char := '{' :: (fragment0180516Field000Chars00 ++ fragment0180516Field001Chars00 ++ fragment0180516Field002Chars00 ++ fragment0180516Field003Chars00 ++ fragment0180516Field004Chars00 ++ fragment0180516Field005Chars00 ++ fragment0180516Field006Chars00 ++ fragment0180516Field007Chars00 ++ fragment0180516Field008Chars00 ++ fragment0180516Field009Chars00)
noncomputable def fragment0180516Value : SourceJson := .obj (fragment0180516Acc01000.reverse)

theorem value_fragment0180516 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 259) (fragment0180516Chars ++ tail) =
      .ok (fragment0180516Value, tail) := by
  have hinput : fragment0180516Chars ++ tail = '{' :: (fragment0180516Field000Chars00 ++ (fragment0180516Field001Chars00 ++ (fragment0180516Field002Chars00 ++ (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0180516Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 259) (fragment0180516Chars ++ tail) =
        SourceJson.value (fuel + 259) ('{' :: (fragment0180516Field000Chars00 ++ (fragment0180516Field001Chars00 ++ (fragment0180516Field002Chars00 ++ (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 259)) hinput
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0180516Field000Chars00 ++ (fragment0180516Field001Chars00 ++ (fragment0180516Field002Chars00 ++ (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))))))))) fragment0180516Acc00000 := by rfl
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0180516Field001Chars00 ++ (fragment0180516Field002Chars00 ++ (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))))))))) fragment0180516Acc00100 := object_fragment0180516_field_000 fuel (fragment0180516Field001Chars00 ++ (fragment0180516Field002Chars00 ++ (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0180516Field002Chars00 ++ (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))))))) fragment0180516Acc00200 := object_fragment0180516_field_001 fuel (fragment0180516Field002Chars00 ++ (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))))))) fragment0180516Acc00300 := object_fragment0180516_field_002 fuel (fragment0180516Field003Chars00 ++ (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))))) fragment0180516Acc00400 := object_fragment0180516_field_003 fuel (fragment0180516Field004Chars00 ++ (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))))) fragment0180516Acc00500 := object_fragment0180516_field_004 fuel (fragment0180516Field005Chars00 ++ (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))) fragment0180516Acc00600 := object_fragment0180516_field_005 fuel (fragment0180516Field006Chars00 ++ (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))) fragment0180516Acc00700 := object_fragment0180516_field_006 fuel (fragment0180516Field007Chars00 ++ (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))) fragment0180516Acc00800 := object_fragment0180516_field_007 fuel (fragment0180516Field008Chars00 ++ (fragment0180516Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0180516Field009Chars00 ++ (tail))) fragment0180516Acc00900 := object_fragment0180516_field_008 fuel (fragment0180516Field009Chars00 ++ (tail))
    _ = .ok (fragment0180516Value, tail) := object_fragment0180516_field_009 fuel (tail)

noncomputable def fragment0182167Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0182167Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0182167Field000Value00 : SourceJson := .number (String.ofList ['4', '5'])
noncomputable def fragment0182167Acc00100 : List (String × SourceJson) := (fragment0182167Field000Key00, fragment0182167Field000Value00) :: fragment0182167Acc00000
noncomputable def fragment0182167Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '5', ',']

theorem object_fragment0182167_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0182167Field000Chars00 ++ tail)) fragment0182167Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0182167Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_000"
  err.flush

noncomputable def fragment0182167Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0182167Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0182167Acc00200 : List (String × SourceJson) := (fragment0182167Field001Key00, fragment0182167Field001Value00) :: fragment0182167Acc00100
noncomputable def fragment0182167Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0182167_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0182167Field001Chars00 ++ tail)) fragment0182167Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0182167Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_001"
  err.flush

noncomputable def fragment0182167Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0182167Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '4', '3', '6', '4', '2', '4', '1', '8', '9', '7', '0', '1', '7', '0', '0', '2', '5', '4', '5', '6', '1', '7', '9', '2', '9', '3', '6', '6', '9', '1', '4', '9', '/', '1', '3', '5', '2', '0', '4', '2', '5', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0182167Acc00300 : List (String × SourceJson) := (fragment0182167Field002Key00, fragment0182167Field002Value00) :: fragment0182167Acc00200
noncomputable def fragment0182167Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '1', '4', '3', '6', '4', '2', '4', '1', '8', '9', '7', '0', '1', '7', '0', '0', '2', '5', '4', '5', '6', '1', '7', '9', '2', '9', '3', '6', '6', '9', '1', '4', '9', '/', '1', '3', '5', '2', '0', '4', '2', '5', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0182167_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0182167Field002Chars00 ++ tail)) fragment0182167Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0182167Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_002"
  err.flush

noncomputable def fragment0182167Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0182167Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0182167Acc00400 : List (String × SourceJson) := (fragment0182167Field003Key00, fragment0182167Field003Value00) :: fragment0182167Acc00300
noncomputable def fragment0182167Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0182167_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0182167Field003Chars00 ++ tail)) fragment0182167Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0182167Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_003"
  err.flush

noncomputable def fragment0182167Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0182167Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0182167Acc00500 : List (String × SourceJson) := (fragment0182167Field004Key00, fragment0182167Field004Value00) :: fragment0182167Acc00400
noncomputable def fragment0182167Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0182167_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0182167Field004Chars00 ++ tail)) fragment0182167Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0182167Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_004"
  err.flush

noncomputable def fragment0182167Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0182167Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '3', '9', '8', '4', '7', '0', '0', '6', '1', '1', '6', '3', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '2', '7', '4', '6', '1', '7', '4', '1', '5', '5', '2', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '3', '7', '6', '2', '0', '8', '0', '7', '9', '5', '2', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '7', '3', '0', '3', '8', '8', '9', '8', '7', '4', '9', '1', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '5', '5', '6', '4', '6', '3', '5', '9', '3', '8', '9', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '2', '8', '3', '3', '9', '6', '7', '0', '2', '1', '3', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '4', '1', '9', '7', '7', '5', '8', '0', '2', '1', '3', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '6', '1', '6', '2', '0', '4', '2', '1', '5', '8', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '9', '2', '6', '0', '5', '2', '5', '5', '5', '1', '2', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '9', '2', '5', '9', '7', '2', '4', '1', '5', '7', '6', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0182167Acc00600 : List (String × SourceJson) := (fragment0182167Field005Key00, fragment0182167Field005Value00) :: fragment0182167Acc00500
noncomputable def fragment0182167Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '8', '4', '7', '0', '0', '6', '1', '1', '6', '3', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '2', '7', '4', '6', '1', '7', '4', '1', '5', '5', '2', '3', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '3', '7', '6', '2', '0', '8', '0', '7', '9', '5', '2', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '7', '3', '0', '3', '8', '8', '9', '8', '7', '4', '9', '1', '/', '4', '0', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '5', '5', '6', '4', '6', '3', '5', '9', '3', '8', '9', '7', '/', '1', '2', '0', '2', '0', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '8', '3', '3', '9', '6', '7', '0', '2', '1', '3', '7', '/', '2', '4', '0', '4', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '4', '1', '9', '7', '7', '5', '8', '0', '2', '1', '3', '/', '2', '0', '0', '3', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '6', '6', '1', '6', '2', '0', '4', '2', '1', '5', '8', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '2', '6', '0', '5', '2', '5', '5', '5', '1', '2', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '2', '5', '9', '7', '2', '4', '1', '5', '7', '6', '1', '/', '6', '0', '1', '0', '4', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0182167_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0182167Field005Chars00 ++ tail)) fragment0182167Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0182167Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_005"
  err.flush

noncomputable def fragment0182167Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0182167Field006Value00 : SourceJson := .str (String.ofList ['2', '9', '1', '8', '7', '4', '0', '4', '4', '6', '7', '0', '0', '2', '8', '8', '2', '4', '6', '1', '1', '1', '8', '1', '7', '4', '6', '7', '0', '0', '8', '8', '2', '0', '5', '8', '1', '9', '0', '8', '4', '8', '0', '0', '0', '0', '0', '/', '7', '0', '0', '8', '2', '6', '0', '3', '6', '6', '2', '2', '1', '1', '4', '9', '9', '8', '8', '4', '1', '8', '5', '0', '4', '0', '9', '6', '4', '6', '3', '2', '6', '4', '8', '6', '1', '4', '2', '8', '7', '3', '1', '0', '7', '3', '6', '0', '3', '0', '1', '7', '8', '8', '7', '3', '3', '2', '5', '4', '5', '6', '4', '3'])
noncomputable def fragment0182167Acc00700 : List (String × SourceJson) := (fragment0182167Field006Key00, fragment0182167Field006Value00) :: fragment0182167Acc00600
noncomputable def fragment0182167Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '9', '1', '8', '7', '4', '0', '4', '4', '6', '7', '0', '0', '2', '8', '8', '2', '4', '6', '1', '1', '1', '8', '1', '7', '4', '6', '7', '0', '0', '8', '8', '2', '0', '5', '8', '1', '9', '0', '8', '4', '8', '0', '0', '0', '0', '0', '/', '7', '0', '0', '8', '2', '6', '0', '3', '6', '6', '2', '2', '1', '1', '4', '9', '9', '8', '8', '4', '1', '8', '5', '0', '4', '0', '9', '6', '4', '6', '3', '2', '6', '4', '8', '6', '1', '4', '2', '8', '7', '3', '1', '0', '7', '3', '6', '0', '3', '0', '1', '7', '8', '8', '7', '3', '3', '2', '5', '4', '5', '6', '4', '3', '"', ',']

theorem object_fragment0182167_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0182167Field006Chars00 ++ tail)) fragment0182167Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0182167Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_006"
  err.flush

noncomputable def fragment0182167Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0182167Field007Value00 : SourceJson := .str (String.ofList ['3', '7', '6', '7', '9', '2', '7', '4', '3', '3', '2', '5', '8', '9', '5', '7', '5', '7', '6', '0', '7', '0', '8', '1', '6', '5', '8', '2', '6', '1', '4', '6', '1', '0', '3', '7', '6', '2', '1', '3', '4', '2', '6', '8', '5', '3', '6', '0', '6', '8', '0', '9', '0', '3', '0', '3', '2', '6', '6', '4', '7', '1', '0', '6', '7', '7', '4', '0', '3', '7', '9', '7', '0', '3', '3', '7', '9', '2', '9', '2', '3', '3', '5', '1', '8', '0', '2', '4', '4', '5', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '2', '1', '9', '5', '9', '8', '4', '5', '6', '0', '4', '4', '2', '3', '4', '6', '1', '6', '5', '7', '0', '9', '2', '1', '9', '4', '5', '1', '6', '5', '2', '2', '9', '4', '0', '6', '7', '1', '1', '4', '3', '4', '3', '5', '9', '9', '3', '6', '1', '0', '4', '1', '4', '5', '6', '4', '8', '7', '7', '5', '4', '0', '3', '4', '3', '3', '0', '3', '9', '9', '1', '5', '1', '6', '5', '3', '2', '3', '9', '4', '3', '6', '8', '7', '4', '5', '5', '4', '4', '9', '0', '4', '7', '4', '7', '5', '4', '7', '5', '7', '5', '8', '0', '6', '3', '5', '2', '9', '3', '2', '0', '7', '5', '9', '2', '8', '2', '8', '8', '8', '1', '1', '2', '5', '8', '9', '9', '3', '4', '3', '1'])
noncomputable def fragment0182167Acc00800 : List (String × SourceJson) := (fragment0182167Field007Key00, fragment0182167Field007Value00) :: fragment0182167Acc00700
noncomputable def fragment0182167Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '6', '7', '9', '2', '7', '4', '3', '3', '2', '5', '8', '9', '5', '7', '5', '7', '6', '0', '7', '0', '8', '1', '6', '5', '8', '2', '6', '1', '4', '6', '1', '0', '3', '7', '6', '2', '1', '3', '4', '2', '6', '8', '5', '3', '6', '0', '6', '8', '0', '9', '0', '3', '0', '3', '2', '6', '6', '4', '7', '1', '0', '6', '7', '7', '4', '0', '3', '7', '9', '7', '0', '3', '3', '7', '9', '2', '9', '2', '3', '3', '5', '1', '8', '0', '2', '4', '4', '5', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '2', '1', '9', '5', '9', '8', '4', '5', '6', '0', '4', '4', '2', '3', '4', '6', '1', '6', '5', '7', '0', '9', '2', '1', '9', '4', '5', '1', '6', '5', '2', '2', '9', '4', '0', '6', '7', '1', '1', '4', '3', '4', '3', '5', '9', '9', '3', '6', '1', '0', '4', '1', '4', '5', '6', '4', '8', '7', '7', '5', '4', '0', '3', '4', '3', '3', '0', '3', '9', '9', '1', '5', '1', '6', '5', '3', '2', '3', '9', '4', '3', '6', '8', '7', '4', '5', '5', '4', '4', '9', '0', '4', '7', '4', '7', '5', '4', '7', '5', '7', '5', '8', '0', '6', '3', '5', '2', '9', '3', '2', '0', '7', '5', '9', '2', '8', '2', '8', '8', '8', '1', '1', '2', '5', '8', '9', '9', '3', '4', '3', '1', '"', ',']

theorem object_fragment0182167_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0182167Field007Chars00 ++ tail)) fragment0182167Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0182167Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_007"
  err.flush

noncomputable def fragment0182167Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0182167Field008Value00 : SourceJson := .str (String.ofList ['3', '2', '9', '9', '6', '2', '6', '8', '7', '4', '0', '6'])
noncomputable def fragment0182167Acc00900 : List (String × SourceJson) := (fragment0182167Field008Key00, fragment0182167Field008Value00) :: fragment0182167Acc00800
noncomputable def fragment0182167Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '9', '9', '6', '2', '6', '8', '7', '4', '0', '6', '"', ',']

theorem object_fragment0182167_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0182167Field008Chars00 ++ tail)) fragment0182167Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0182167Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_008"
  err.flush

noncomputable def fragment0182167Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0182167Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '3', '7', '0', '6', '2', '6', '5', '3', '6', '5'])
noncomputable def fragment0182167Acc01000 : List (String × SourceJson) := (fragment0182167Field009Key00, fragment0182167Field009Value00) :: fragment0182167Acc00900
noncomputable def fragment0182167Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '3', '7', '0', '6', '2', '6', '5', '3', '6', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0182167_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0182167Field009Chars00 ++ tail)) fragment0182167Acc00900 =
      .ok (.obj (fragment0182167Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182167_object_field_009"
  err.flush

noncomputable def fragment0182167Chars : List Char := '{' :: (fragment0182167Field000Chars00 ++ fragment0182167Field001Chars00 ++ fragment0182167Field002Chars00 ++ fragment0182167Field003Chars00 ++ fragment0182167Field004Chars00 ++ fragment0182167Field005Chars00 ++ fragment0182167Field006Chars00 ++ fragment0182167Field007Chars00 ++ fragment0182167Field008Chars00 ++ fragment0182167Field009Chars00)
noncomputable def fragment0182167Value : SourceJson := .obj (fragment0182167Acc01000.reverse)

theorem value_fragment0182167 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0182167Chars ++ tail) =
      .ok (fragment0182167Value, tail) := by
  have hinput : fragment0182167Chars ++ tail = '{' :: (fragment0182167Field000Chars00 ++ (fragment0182167Field001Chars00 ++ (fragment0182167Field002Chars00 ++ (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0182167Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0182167Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0182167Field000Chars00 ++ (fragment0182167Field001Chars00 ++ (fragment0182167Field002Chars00 ++ (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0182167Field000Chars00 ++ (fragment0182167Field001Chars00 ++ (fragment0182167Field002Chars00 ++ (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))))))))) fragment0182167Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0182167Field001Chars00 ++ (fragment0182167Field002Chars00 ++ (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))))))))) fragment0182167Acc00100 := object_fragment0182167_field_000 fuel (fragment0182167Field001Chars00 ++ (fragment0182167Field002Chars00 ++ (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0182167Field002Chars00 ++ (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))))))) fragment0182167Acc00200 := object_fragment0182167_field_001 fuel (fragment0182167Field002Chars00 ++ (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))))))) fragment0182167Acc00300 := object_fragment0182167_field_002 fuel (fragment0182167Field003Chars00 ++ (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))))) fragment0182167Acc00400 := object_fragment0182167_field_003 fuel (fragment0182167Field004Chars00 ++ (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))))) fragment0182167Acc00500 := object_fragment0182167_field_004 fuel (fragment0182167Field005Chars00 ++ (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))) fragment0182167Acc00600 := object_fragment0182167_field_005 fuel (fragment0182167Field006Chars00 ++ (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))) fragment0182167Acc00700 := object_fragment0182167_field_006 fuel (fragment0182167Field007Chars00 ++ (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))) fragment0182167Acc00800 := object_fragment0182167_field_007 fuel (fragment0182167Field008Chars00 ++ (fragment0182167Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0182167Field009Chars00 ++ (tail))) fragment0182167Acc00900 := object_fragment0182167_field_008 fuel (fragment0182167Field009Chars00 ++ (tail))
    _ = .ok (fragment0182167Value, tail) := object_fragment0182167_field_009 fuel (tail)

noncomputable def fragment0183810Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0183810Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0183810Field000Value00 : SourceJson := .number (String.ofList ['4', '6'])
noncomputable def fragment0183810Acc00100 : List (String × SourceJson) := (fragment0183810Field000Key00, fragment0183810Field000Value00) :: fragment0183810Acc00000
noncomputable def fragment0183810Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '6', ',']

theorem object_fragment0183810_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 282) (SourceJson.white (fragment0183810Field000Chars00 ++ tail)) fragment0183810Acc00000 =
      SourceJson.object (fuel + 281) (SourceJson.white tail) fragment0183810Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_000"
  err.flush

noncomputable def fragment0183810Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0183810Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['1'])]
noncomputable def fragment0183810Acc00200 : List (String × SourceJson) := (fragment0183810Field001Key00, fragment0183810Field001Value00) :: fragment0183810Acc00100
noncomputable def fragment0183810Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0183810_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 281) (SourceJson.white (fragment0183810Field001Chars00 ++ tail)) fragment0183810Acc00100 =
      SourceJson.object (fuel + 280) (SourceJson.white tail) fragment0183810Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_001"
  err.flush

noncomputable def fragment0183810Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0183810Field002Value00 : SourceJson := .str (String.ofList ['2', '6', '9', '2', '4', '4', '3', '4', '1', '3', '6', '1', '2', '1', '9', '7', '1', '5', '8', '6', '9', '2', '1', '2', '9', '7', '1', '6', '5', '9', '4', '1', '3', '/', '4', '0', '3', '7', '3', '4', '9', '4', '0', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0183810Acc00300 : List (String × SourceJson) := (fragment0183810Field002Key00, fragment0183810Field002Value00) :: fragment0183810Acc00200
noncomputable def fragment0183810Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '6', '9', '2', '4', '4', '3', '4', '1', '3', '6', '1', '2', '1', '9', '7', '1', '5', '8', '6', '9', '2', '1', '2', '9', '7', '1', '6', '5', '9', '4', '1', '3', '/', '4', '0', '3', '7', '3', '4', '9', '4', '0', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0183810_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 280) (SourceJson.white (fragment0183810Field002Chars00 ++ tail)) fragment0183810Acc00200 =
      SourceJson.object (fuel + 279) (SourceJson.white tail) fragment0183810Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_002"
  err.flush

noncomputable def fragment0183810Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0183810Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0183810Acc00400 : List (String × SourceJson) := (fragment0183810Field003Key00, fragment0183810Field003Value00) :: fragment0183810Acc00300
noncomputable def fragment0183810Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0183810_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 279) (SourceJson.white (fragment0183810Field003Chars00 ++ tail)) fragment0183810Acc00300 =
      SourceJson.object (fuel + 278) (SourceJson.white tail) fragment0183810Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_003"
  err.flush

noncomputable def fragment0183810Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0183810Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0183810Acc00500 : List (String × SourceJson) := (fragment0183810Field004Key00, fragment0183810Field004Value00) :: fragment0183810Acc00400
noncomputable def fragment0183810Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '7', '3', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '8', '6', '9', '/', '6', '1', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '9', '9', '9', '1', '/', '3', '0', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0183810_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 278) (SourceJson.white (fragment0183810Field004Chars00 ++ tail)) fragment0183810Acc00400 =
      SourceJson.object (fuel + 277) (SourceJson.white tail) fragment0183810Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_004"
  err.flush

noncomputable def fragment0183810Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0183810Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '3', '8', '5', '4', '7', '1', '6', '6', '5', '9', '1', '9', '3', '7', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '6', '1', '9', '5', '0', '9', '4', '4', '6', '8', '8', '9', '3', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '4', '3', '0', '1', '5', '3', '7', '0', '8', '9', '9', '3', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '7', '3', '1', '5', '4', '0', '9', '6', '6', '2', '7', '5', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '4', '4', '8', '7', '4', '5', '8', '8', '0', '7', '4', '3', '9', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '2', '3', '9', '5', '7', '0', '5', '0', '8', '3', '8', '7', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '0', '1', '4', '2', '7', '0', '1', '0', '2', '3', '9', '2', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '5', '5', '2', '5', '4', '8', '2', '6', '0', '5', '2', '7', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '8', '8', '3', '8', '7', '4', '4', '3', '7', '2', '6', '1', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '8', '8', '3', '4', '4', '3', '6', '8', '8', '2', '0', '1', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0183810Acc00600 : List (String × SourceJson) := (fragment0183810Field005Key00, fragment0183810Field005Value00) :: fragment0183810Acc00500
noncomputable def fragment0183810Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '8', '5', '4', '7', '1', '6', '6', '5', '9', '1', '9', '3', '7', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '1', '9', '5', '0', '9', '4', '4', '6', '8', '8', '9', '3', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '4', '3', '0', '1', '5', '3', '7', '0', '8', '9', '9', '3', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '7', '3', '1', '5', '4', '0', '9', '6', '6', '2', '7', '5', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '4', '4', '8', '7', '4', '5', '8', '8', '0', '7', '4', '3', '9', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '3', '9', '5', '7', '0', '5', '0', '8', '3', '8', '7', '/', '2', '8', '7', '1', '6', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '0', '1', '4', '2', '7', '0', '1', '0', '2', '3', '9', '2', '1', '/', '1', '2', '9', '2', '2', '4', '7', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '5', '5', '2', '5', '4', '8', '2', '6', '0', '5', '2', '7', '/', '6', '4', '6', '1', '2', '3', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '8', '8', '3', '8', '7', '4', '4', '3', '7', '2', '6', '1', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '8', '8', '3', '4', '4', '3', '6', '8', '8', '2', '0', '1', '/', '3', '2', '3', '0', '6', '1', '7', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0183810_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment0183810Field005Chars00 ++ tail)) fragment0183810Acc00500 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment0183810Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_005"
  err.flush

noncomputable def fragment0183810Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0183810Field006Value00 : SourceJson := .str (String.ofList ['9', '9', '0', '3', '3', '4', '2', '4', '7', '1', '1', '6', '0', '8', '7', '8', '6', '1', '4', '7', '7', '7', '5', '1', '1', '1', '9', '1', '3', '5', '0', '9', '2', '2', '6', '3', '6', '3', '9', '8', '8', '4', '1', '5', '4', '0', '0', '0', '0', '0', '0', '/', '2', '8', '2', '5', '9', '5', '7', '3', '6', '2', '7', '9', '0', '3', '3', '3', '7', '6', '6', '4', '9', '1', '7', '7', '8', '9', '4', '2', '7', '0', '9', '0', '0', '9', '8', '6', '5', '9', '1', '8', '7', '3', '8', '6', '9', '3', '2', '9', '2', '2', '8', '3', '4', '8', '7', '3', '8', '3', '9', '3', '5', '3', '2', '2', '0', '1', '1', '6', '9'])
noncomputable def fragment0183810Acc00700 : List (String × SourceJson) := (fragment0183810Field006Key00, fragment0183810Field006Value00) :: fragment0183810Acc00600
noncomputable def fragment0183810Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '9', '0', '3', '3', '4', '2', '4', '7', '1', '1', '6', '0', '8', '7', '8', '6', '1', '4', '7', '7', '7', '5', '1', '1', '1', '9', '1', '3', '5', '0', '9', '2', '2', '6', '3', '6', '3', '9', '8', '8', '4', '1', '5', '4', '0', '0', '0', '0', '0', '0', '/', '2', '8', '2', '5', '9', '5', '7', '3', '6', '2', '7', '9', '0', '3', '3', '3', '7', '6', '6', '4', '9', '1', '7', '7', '8', '9', '4', '2', '7', '0', '9', '0', '0', '9', '8', '6', '5', '9', '1', '8', '7', '3', '8', '6', '9', '3', '2', '9', '2', '2', '8', '3', '4', '8', '7', '3', '8', '3', '9', '3', '5', '3', '2', '2', '0', '1', '1', '6', '9', '"', ',']

theorem object_fragment0183810_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment0183810Field006Chars00 ++ tail)) fragment0183810Acc00600 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment0183810Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_006"
  err.flush

noncomputable def fragment0183810Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0183810Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '3', '7', '2', '3', '2', '9', '4', '6', '7', '0', '3', '7', '0', '0', '1', '6', '7', '2', '4', '8', '5', '7', '0', '4', '2', '4', '1', '2', '0', '2', '5', '8', '3', '8', '1', '2', '4', '0', '8', '1', '1', '7', '5', '7', '9', '3', '0', '5', '5', '6', '3', '1', '5', '5', '9', '3', '5', '5', '7', '0', '8', '5', '8', '1', '6', '7', '3', '5', '2', '0', '7', '3', '8', '0', '2', '6', '6', '2', '3', '6', '2', '1', '7', '4', '4', '4', '8', '7', '4', '7', '8', '1', '2', '7', '3', '6', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '9', '9', '1', '9', '3', '1', '4', '3', '6', '2', '4', '4', '3', '3', '1', '3', '5', '6', '4', '2', '5', '3', '1', '2', '9', '6', '6', '1', '5', '1', '7', '8', '5', '4', '5', '5', '3', '6', '6', '8', '6', '0', '2', '7', '5', '9', '4', '1', '2', '0', '5', '9', '9', '0', '7', '4', '6', '5', '6', '7', '7', '0', '7', '3', '7', '3', '4', '8', '8', '4', '2', '7', '0', '4', '2', '8', '5', '1', '6', '1', '5', '4', '8', '4', '9', '4', '1', '9', '8', '3', '7', '6', '2', '8', '4', '3', '8', '5', '6', '7', '1', '6', '0', '5', '9', '5', '2', '0', '0', '2', '5', '0', '4', '4', '1', '4', '5', '7', '7', '2', '9', '5', '1', '9', '4', '5', '4', '8', '8', '0', '8', '0', '0', '0', '3', '7', '0', '5', '5', '3', '1', '1'])
noncomputable def fragment0183810Acc00800 : List (String × SourceJson) := (fragment0183810Field007Key00, fragment0183810Field007Value00) :: fragment0183810Acc00700
noncomputable def fragment0183810Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '9', '3', '7', '2', '3', '2', '9', '4', '6', '7', '0', '3', '7', '0', '0', '1', '6', '7', '2', '4', '8', '5', '7', '0', '4', '2', '4', '1', '2', '0', '2', '5', '8', '3', '8', '1', '2', '4', '0', '8', '1', '1', '7', '5', '7', '9', '3', '0', '5', '5', '6', '3', '1', '5', '5', '9', '3', '5', '5', '7', '0', '8', '5', '8', '1', '6', '7', '3', '5', '2', '0', '7', '3', '8', '0', '2', '6', '6', '2', '3', '6', '2', '1', '7', '4', '4', '4', '8', '7', '4', '7', '8', '1', '2', '7', '3', '6', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '9', '9', '1', '9', '3', '1', '4', '3', '6', '2', '4', '4', '3', '3', '1', '3', '5', '6', '4', '2', '5', '3', '1', '2', '9', '6', '6', '1', '5', '1', '7', '8', '5', '4', '5', '5', '3', '6', '6', '8', '6', '0', '2', '7', '5', '9', '4', '1', '2', '0', '5', '9', '9', '0', '7', '4', '6', '5', '6', '7', '7', '0', '7', '3', '7', '3', '4', '8', '8', '4', '2', '7', '0', '4', '2', '8', '5', '1', '6', '1', '5', '4', '8', '4', '9', '4', '1', '9', '8', '3', '7', '6', '2', '8', '4', '3', '8', '5', '6', '7', '1', '6', '0', '5', '9', '5', '2', '0', '0', '2', '5', '0', '4', '4', '1', '4', '5', '7', '7', '2', '9', '5', '1', '9', '4', '5', '4', '8', '8', '0', '8', '0', '0', '0', '3', '7', '0', '5', '5', '3', '1', '1', '"', ',']

theorem object_fragment0183810_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment0183810Field007Chars00 ++ tail)) fragment0183810Acc00700 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment0183810Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_007"
  err.flush

noncomputable def fragment0183810Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0183810Field008Value00 : SourceJson := .str (String.ofList ['2', '7', '7', '6', '4', '8', '7', '8', '4', '4', '6', '8'])
noncomputable def fragment0183810Acc00900 : List (String × SourceJson) := (fragment0183810Field008Key00, fragment0183810Field008Value00) :: fragment0183810Acc00800
noncomputable def fragment0183810Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '7', '6', '4', '8', '7', '8', '4', '4', '6', '8', '"', ',']

theorem object_fragment0183810_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment0183810Field008Chars00 ++ tail)) fragment0183810Acc00800 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment0183810Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_008"
  err.flush

noncomputable def fragment0183810Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0183810Field009Value00 : SourceJson := .str (String.ofList ['8', '6', '0', '4', '1', '7', '5', '1', '3', '8', '4', '4'])
noncomputable def fragment0183810Acc01000 : List (String × SourceJson) := (fragment0183810Field009Key00, fragment0183810Field009Value00) :: fragment0183810Acc00900
noncomputable def fragment0183810Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '0', '4', '1', '7', '5', '1', '3', '8', '4', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0183810_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment0183810Field009Chars00 ++ tail)) fragment0183810Acc00900 =
      .ok (.obj (fragment0183810Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183810_object_field_009"
  err.flush

noncomputable def fragment0183810Chars : List Char := '{' :: (fragment0183810Field000Chars00 ++ fragment0183810Field001Chars00 ++ fragment0183810Field002Chars00 ++ fragment0183810Field003Chars00 ++ fragment0183810Field004Chars00 ++ fragment0183810Field005Chars00 ++ fragment0183810Field006Chars00 ++ fragment0183810Field007Chars00 ++ fragment0183810Field008Chars00 ++ fragment0183810Field009Chars00)
noncomputable def fragment0183810Value : SourceJson := .obj (fragment0183810Acc01000.reverse)

theorem value_fragment0183810 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 283) (fragment0183810Chars ++ tail) =
      .ok (fragment0183810Value, tail) := by
  have hinput : fragment0183810Chars ++ tail = '{' :: (fragment0183810Field000Chars00 ++ (fragment0183810Field001Chars00 ++ (fragment0183810Field002Chars00 ++ (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0183810Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 283) (fragment0183810Chars ++ tail) =
        SourceJson.value (fuel + 283) ('{' :: (fragment0183810Field000Chars00 ++ (fragment0183810Field001Chars00 ++ (fragment0183810Field002Chars00 ++ (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 283)) hinput
    _ = SourceJson.object (fuel + 282) (SourceJson.white (fragment0183810Field000Chars00 ++ (fragment0183810Field001Chars00 ++ (fragment0183810Field002Chars00 ++ (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))))))))) fragment0183810Acc00000 := by rfl
    _ = SourceJson.object (fuel + 281) (SourceJson.white (fragment0183810Field001Chars00 ++ (fragment0183810Field002Chars00 ++ (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))))))))) fragment0183810Acc00100 := object_fragment0183810_field_000 fuel (fragment0183810Field001Chars00 ++ (fragment0183810Field002Chars00 ++ (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 280) (SourceJson.white (fragment0183810Field002Chars00 ++ (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))))))) fragment0183810Acc00200 := object_fragment0183810_field_001 fuel (fragment0183810Field002Chars00 ++ (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 279) (SourceJson.white (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))))))) fragment0183810Acc00300 := object_fragment0183810_field_002 fuel (fragment0183810Field003Chars00 ++ (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 278) (SourceJson.white (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))))) fragment0183810Acc00400 := object_fragment0183810_field_003 fuel (fragment0183810Field004Chars00 ++ (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))))) fragment0183810Acc00500 := object_fragment0183810_field_004 fuel (fragment0183810Field005Chars00 ++ (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))) fragment0183810Acc00600 := object_fragment0183810_field_005 fuel (fragment0183810Field006Chars00 ++ (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))) fragment0183810Acc00700 := object_fragment0183810_field_006 fuel (fragment0183810Field007Chars00 ++ (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))) fragment0183810Acc00800 := object_fragment0183810_field_007 fuel (fragment0183810Field008Chars00 ++ (fragment0183810Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment0183810Field009Chars00 ++ (tail))) fragment0183810Acc00900 := object_fragment0183810_field_008 fuel (fragment0183810Field009Chars00 ++ (tail))
    _ = .ok (fragment0183810Value, tail) := object_fragment0183810_field_009 fuel (tail)

noncomputable def fragment0185498Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0185498Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0185498Field000Value00 : SourceJson := .number (String.ofList ['4', '7'])
noncomputable def fragment0185498Acc00100 : List (String × SourceJson) := (fragment0185498Field000Key00, fragment0185498Field000Value00) :: fragment0185498Acc00000
noncomputable def fragment0185498Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '7', ',']

theorem object_fragment0185498_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0185498Field000Chars00 ++ tail)) fragment0185498Acc00000 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0185498Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_000"
  err.flush

noncomputable def fragment0185498Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0185498Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['5']), .number (String.ofList ['1'])]
noncomputable def fragment0185498Acc00200 : List (String × SourceJson) := (fragment0185498Field001Key00, fragment0185498Field001Value00) :: fragment0185498Acc00100
noncomputable def fragment0185498Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0185498_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0185498Field001Chars00 ++ tail)) fragment0185498Acc00100 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0185498Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_001"
  err.flush

noncomputable def fragment0185498Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0185498Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '6', '9', '6', '7', '5', '9', '3', '4', '9', '1', '3', '4', '7', '6', '1', '5', '2', '7', '7', '7', '1', '3', '0', '2', '9', '9', '9', '4', '8', '1', '/', '2', '4', '8', '1', '9', '7', '7', '0', '9', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0185498Acc00300 : List (String × SourceJson) := (fragment0185498Field002Key00, fragment0185498Field002Value00) :: fragment0185498Acc00200
noncomputable def fragment0185498Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '1', '6', '9', '6', '7', '5', '9', '3', '4', '9', '1', '3', '4', '7', '6', '1', '5', '2', '7', '7', '7', '1', '3', '0', '2', '9', '9', '9', '4', '8', '1', '/', '2', '4', '8', '1', '9', '7', '7', '0', '9', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0185498_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0185498Field002Chars00 ++ tail)) fragment0185498Acc00200 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0185498Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_002"
  err.flush

noncomputable def fragment0185498Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0185498Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0185498Acc00400 : List (String × SourceJson) := (fragment0185498Field003Key00, fragment0185498Field003Value00) :: fragment0185498Acc00300
noncomputable def fragment0185498Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0185498_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0185498Field003Chars00 ++ tail)) fragment0185498Acc00300 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0185498Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_003"
  err.flush

noncomputable def fragment0185498Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0185498Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0185498Acc00500 : List (String × SourceJson) := (fragment0185498Field004Key00, fragment0185498Field004Value00) :: fragment0185498Acc00400
noncomputable def fragment0185498Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '4', '4', '0', '3', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '1', '0', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '8', '1', '1', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '6', '7', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0185498_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0185498Field004Chars00 ++ tail)) fragment0185498Acc00400 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0185498Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_004"
  err.flush

noncomputable def fragment0185498Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0185498Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '1', '5', '9', '4', '2', '5', '5', '1', '3', '5', '3', '1', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '2', '1', '0', '3', '4', '8', '1', '8', '5', '9', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '4', '7', '6', '5', '5', '3', '6', '1', '6', '9', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '4', '5', '9', '1', '2', '9', '2', '0', '7', '6', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '3', '2', '8', '3', '4', '0', '7', '6', '7', '2', '7', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '6', '8', '8', '6', '7', '4', '6', '5', '5', '7', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '6', '7', '4', '4', '3', '8', '6', '1', '5', '5', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '7', '9', '3', '4', '9', '9', '4', '5', '2', '0', '9', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '3', '4', '4', '7', '6', '7', '1', '7', '5', '1', '9', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '3', '4', '4', '4', '8', '4', '7', '1', '6', '7', '9', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0185498Acc00600 : List (String × SourceJson) := (fragment0185498Field005Key00, fragment0185498Field005Value00) :: fragment0185498Acc00500
noncomputable def fragment0185498Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '9', '4', '2', '5', '5', '1', '3', '5', '3', '1', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '2', '1', '0', '3', '4', '8', '1', '8', '5', '9', '7', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '4', '7', '6', '5', '5', '3', '6', '1', '6', '9', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '4', '5', '9', '1', '2', '9', '2', '0', '7', '6', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '3', '2', '8', '3', '4', '0', '7', '6', '7', '2', '7', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '6', '8', '8', '6', '7', '4', '6', '5', '5', '7', '/', '1', '4', '1', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '7', '4', '4', '3', '8', '6', '1', '5', '5', '3', '/', '1', '0', '5', '9', '2', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '7', '9', '3', '4', '9', '9', '4', '5', '2', '0', '9', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '3', '4', '4', '7', '6', '7', '1', '7', '5', '1', '9', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '3', '4', '4', '4', '8', '4', '7', '1', '6', '7', '9', '/', '2', '1', '1', '8', '4', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0185498_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0185498Field005Chars00 ++ tail)) fragment0185498Acc00500 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0185498Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_005"
  err.flush

noncomputable def fragment0185498Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0185498Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '9', '2', '7', '2', '5', '3', '1', '3', '0', '4', '9', '3', '2', '3', '0', '2', '1', '1', '7', '7', '0', '9', '1', '3', '0', '4', '2', '3', '5', '6', '5', '1', '9', '8', '7', '5', '3', '7', '9', '2', '0', '0', '0', '0', '0', '/', '3', '1', '1', '9', '5', '7', '5', '4', '9', '7', '7', '5', '4', '3', '3', '7', '1', '3', '7', '0', '6', '0', '1', '5', '6', '7', '0', '7', '2', '7', '8', '2', '9', '7', '4', '3', '6', '8', '6', '0', '2', '3', '8', '9', '4', '9', '6', '6', '0', '4', '0', '1', '2', '5', '7', '8', '6', '1', '0', '0', '6', '4', '5', '4', '3'])
noncomputable def fragment0185498Acc00700 : List (String × SourceJson) := (fragment0185498Field006Key00, fragment0185498Field006Value00) :: fragment0185498Acc00600
noncomputable def fragment0185498Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '3', '9', '2', '7', '2', '5', '3', '1', '3', '0', '4', '9', '3', '2', '3', '0', '2', '1', '1', '7', '7', '0', '9', '1', '3', '0', '4', '2', '3', '5', '6', '5', '1', '9', '8', '7', '5', '3', '7', '9', '2', '0', '0', '0', '0', '0', '/', '3', '1', '1', '9', '5', '7', '5', '4', '9', '7', '7', '5', '4', '3', '3', '7', '1', '3', '7', '0', '6', '0', '1', '5', '6', '7', '0', '7', '2', '7', '8', '2', '9', '7', '4', '3', '6', '8', '6', '0', '2', '3', '8', '9', '4', '9', '6', '6', '0', '4', '0', '1', '2', '5', '7', '8', '6', '1', '0', '0', '6', '4', '5', '4', '3', '"', ',']

theorem object_fragment0185498_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0185498Field006Chars00 ++ tail)) fragment0185498Acc00600 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0185498Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_006"
  err.flush

noncomputable def fragment0185498Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0185498Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '9', '4', '3', '6', '0', '9', '4', '1', '1', '8', '1', '7', '0', '0', '8', '9', '2', '9', '5', '2', '9', '0', '0', '0', '9', '4', '1', '3', '2', '4', '9', '6', '0', '0', '2', '4', '5', '6', '0', '8', '4', '5', '3', '5', '1', '6', '4', '6', '6', '3', '6', '5', '0', '0', '4', '5', '7', '9', '1', '8', '1', '5', '4', '5', '5', '4', '0', '6', '3', '0', '0', '2', '8', '3', '5', '6', '3', '0', '4', '6', '3', '3', '1', '8', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '3', '4', '4', '9', '0', '4', '3', '9', '6', '4', '9', '3', '0', '5', '4', '2', '8', '5', '1', '1', '8', '7', '0', '5', '4', '5', '8', '7', '9', '7', '2', '4', '4', '1', '0', '9', '2', '1', '2', '2', '7', '1', '5', '9', '0', '7', '6', '7', '6', '0', '5', '8', '6', '1', '7', '6', '4', '2', '6', '8', '1', '2', '9', '7', '2', '9', '4', '5', '0', '2', '3', '7', '5', '2', '5', '5', '6', '9', '1', '7', '9', '9', '2', '8', '9', '3', '2', '8', '4', '9', '8', '1', '7', '8', '8', '8', '3', '2', '1', '3', '1', '8', '5', '5', '2', '0', '9', '9', '7', '3', '6', '9', '7', '1', '3', '6', '4', '0', '9', '7', '2', '3', '9', '8', '8', '7'])
noncomputable def fragment0185498Acc00800 : List (String × SourceJson) := (fragment0185498Field007Key00, fragment0185498Field007Value00) :: fragment0185498Acc00700
noncomputable def fragment0185498Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '9', '4', '3', '6', '0', '9', '4', '1', '1', '8', '1', '7', '0', '0', '8', '9', '2', '9', '5', '2', '9', '0', '0', '0', '9', '4', '1', '3', '2', '4', '9', '6', '0', '0', '2', '4', '5', '6', '0', '8', '4', '5', '3', '5', '1', '6', '4', '6', '6', '3', '6', '5', '0', '0', '4', '5', '7', '9', '1', '8', '1', '5', '4', '5', '5', '4', '0', '6', '3', '0', '0', '2', '8', '3', '5', '6', '3', '0', '4', '6', '3', '3', '1', '8', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '3', '4', '4', '9', '0', '4', '3', '9', '6', '4', '9', '3', '0', '5', '4', '2', '8', '5', '1', '1', '8', '7', '0', '5', '4', '5', '8', '7', '9', '7', '2', '4', '4', '1', '0', '9', '2', '1', '2', '2', '7', '1', '5', '9', '0', '7', '6', '7', '6', '0', '5', '8', '6', '1', '7', '6', '4', '2', '6', '8', '1', '2', '9', '7', '2', '9', '4', '5', '0', '2', '3', '7', '5', '2', '5', '5', '6', '9', '1', '7', '9', '9', '2', '8', '9', '3', '2', '8', '4', '9', '8', '1', '7', '8', '8', '8', '3', '2', '1', '3', '1', '8', '5', '5', '2', '0', '9', '9', '7', '3', '6', '9', '7', '1', '3', '6', '4', '0', '9', '7', '2', '3', '9', '8', '8', '7', '"', ',']

theorem object_fragment0185498_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0185498Field007Chars00 ++ tail)) fragment0185498Acc00700 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0185498Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_007"
  err.flush

noncomputable def fragment0185498Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0185498Field008Value00 : SourceJson := .str (String.ofList ['2', '6', '3', '9', '4', '5', '0', '5', '6', '1', '9', '7'])
noncomputable def fragment0185498Acc00900 : List (String × SourceJson) := (fragment0185498Field008Key00, fragment0185498Field008Value00) :: fragment0185498Acc00800
noncomputable def fragment0185498Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '3', '9', '4', '5', '0', '5', '6', '1', '9', '7', '"', ',']

theorem object_fragment0185498_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0185498Field008Chars00 ++ tail)) fragment0185498Acc00800 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0185498Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_008"
  err.flush

noncomputable def fragment0185498Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0185498Field009Value00 : SourceJson := .str (String.ofList ['7', '8', '2', '1', '3', '8', '3', '9', '2', '9', '7', '3'])
noncomputable def fragment0185498Acc01000 : List (String × SourceJson) := (fragment0185498Field009Key00, fragment0185498Field009Value00) :: fragment0185498Acc00900
noncomputable def fragment0185498Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '8', '2', '1', '3', '8', '3', '9', '2', '9', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0185498_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0185498Field009Chars00 ++ tail)) fragment0185498Acc00900 =
      .ok (.obj (fragment0185498Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185498_object_field_009"
  err.flush

noncomputable def fragment0185498Chars : List Char := '{' :: (fragment0185498Field000Chars00 ++ fragment0185498Field001Chars00 ++ fragment0185498Field002Chars00 ++ fragment0185498Field003Chars00 ++ fragment0185498Field004Chars00 ++ fragment0185498Field005Chars00 ++ fragment0185498Field006Chars00 ++ fragment0185498Field007Chars00 ++ fragment0185498Field008Chars00 ++ fragment0185498Field009Chars00)
noncomputable def fragment0185498Value : SourceJson := .obj (fragment0185498Acc01000.reverse)

theorem value_fragment0185498 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 251) (fragment0185498Chars ++ tail) =
      .ok (fragment0185498Value, tail) := by
  have hinput : fragment0185498Chars ++ tail = '{' :: (fragment0185498Field000Chars00 ++ (fragment0185498Field001Chars00 ++ (fragment0185498Field002Chars00 ++ (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0185498Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 251) (fragment0185498Chars ++ tail) =
        SourceJson.value (fuel + 251) ('{' :: (fragment0185498Field000Chars00 ++ (fragment0185498Field001Chars00 ++ (fragment0185498Field002Chars00 ++ (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 251)) hinput
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0185498Field000Chars00 ++ (fragment0185498Field001Chars00 ++ (fragment0185498Field002Chars00 ++ (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))))))))) fragment0185498Acc00000 := by rfl
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0185498Field001Chars00 ++ (fragment0185498Field002Chars00 ++ (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))))))))) fragment0185498Acc00100 := object_fragment0185498_field_000 fuel (fragment0185498Field001Chars00 ++ (fragment0185498Field002Chars00 ++ (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0185498Field002Chars00 ++ (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))))))) fragment0185498Acc00200 := object_fragment0185498_field_001 fuel (fragment0185498Field002Chars00 ++ (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))))))) fragment0185498Acc00300 := object_fragment0185498_field_002 fuel (fragment0185498Field003Chars00 ++ (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))))) fragment0185498Acc00400 := object_fragment0185498_field_003 fuel (fragment0185498Field004Chars00 ++ (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))))) fragment0185498Acc00500 := object_fragment0185498_field_004 fuel (fragment0185498Field005Chars00 ++ (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))) fragment0185498Acc00600 := object_fragment0185498_field_005 fuel (fragment0185498Field006Chars00 ++ (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))) fragment0185498Acc00700 := object_fragment0185498_field_006 fuel (fragment0185498Field007Chars00 ++ (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))) fragment0185498Acc00800 := object_fragment0185498_field_007 fuel (fragment0185498Field008Chars00 ++ (fragment0185498Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0185498Field009Chars00 ++ (tail))) fragment0185498Acc00900 := object_fragment0185498_field_008 fuel (fragment0185498Field009Chars00 ++ (tail))
    _ = .ok (fragment0185498Value, tail) := object_fragment0185498_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_before_reader"
  err.flush

noncomputable def chunk0040LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0040SuffixChars00 : List Char := [',']
noncomputable def chunk0040Chars00 : List Char := chunk0040LeadChars00 ++ fragment0173580Chars ++ chunk0040SuffixChars00
noncomputable def chunk0040Push00 (acc : List SourceJson) : List SourceJson := fragment0173580Value :: acc

noncomputable def chunk0040AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0040_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 433)
      (SourceJson.white (chunk0040LeadChars00 ++ (fragment0173580Chars ++ rest))) acc =
      (SourceJson.value (fuel + 432) (fragment0173580Chars ++ rest)).bind
        (chunk0040AfterValue00 (fuel + 432) acc) := by rfl

theorem array_chunk0040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 433) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 432) (SourceJson.white tail) (chunk0040Push00 acc) := by
  have hinput : chunk0040Chars00 ++ tail = chunk0040LeadChars00 ++ (fragment0173580Chars ++ (chunk0040SuffixChars00 ++ tail)) := by
    simp only [chunk0040Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 433) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 433)
          (SourceJson.white (chunk0040LeadChars00 ++ (fragment0173580Chars ++ (chunk0040SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 433) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 432) (fragment0173580Chars ++ (chunk0040SuffixChars00 ++ tail))).bind
        (chunk0040AfterValue00 (fuel + 432) acc) := array_chunk0040_head fuel (chunk0040SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0173580Value, chunk0040SuffixChars00 ++ tail)).bind
        (chunk0040AfterValue00 (fuel + 432) acc) :=
      congrArg (fun result => result.bind (chunk0040AfterValue00 (fuel + 432) acc))
        (value_fragment0173580 (fuel + 138) (chunk0040SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 432) (SourceJson.white tail) (chunk0040Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_before_reader"
  err.flush

noncomputable def chunk0041LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0041SuffixChars00 : List Char := [',']
noncomputable def chunk0041Chars00 : List Char := chunk0041LeadChars00 ++ fragment0175302Chars ++ chunk0041SuffixChars00
noncomputable def chunk0041Push00 (acc : List SourceJson) : List SourceJson := fragment0175302Value :: acc

noncomputable def chunk0041AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0041_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 432)
      (SourceJson.white (chunk0041LeadChars00 ++ (fragment0175302Chars ++ rest))) acc =
      (SourceJson.value (fuel + 431) (fragment0175302Chars ++ rest)).bind
        (chunk0041AfterValue00 (fuel + 431) acc) := by rfl

theorem array_chunk0041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 432) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 431) (SourceJson.white tail) (chunk0041Push00 acc) := by
  have hinput : chunk0041Chars00 ++ tail = chunk0041LeadChars00 ++ (fragment0175302Chars ++ (chunk0041SuffixChars00 ++ tail)) := by
    simp only [chunk0041Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 432) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 432)
          (SourceJson.white (chunk0041LeadChars00 ++ (fragment0175302Chars ++ (chunk0041SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 432) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 431) (fragment0175302Chars ++ (chunk0041SuffixChars00 ++ tail))).bind
        (chunk0041AfterValue00 (fuel + 431) acc) := array_chunk0041_head fuel (chunk0041SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0175302Value, chunk0041SuffixChars00 ++ tail)).bind
        (chunk0041AfterValue00 (fuel + 431) acc) :=
      congrArg (fun result => result.bind (chunk0041AfterValue00 (fuel + 431) acc))
        (value_fragment0175302 (fuel + 176) (chunk0041SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 431) (SourceJson.white tail) (chunk0041Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_before_reader"
  err.flush

noncomputable def chunk0042LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0042SuffixChars00 : List Char := [',']
noncomputable def chunk0042Chars00 : List Char := chunk0042LeadChars00 ++ fragment0176947Chars ++ chunk0042SuffixChars00
noncomputable def chunk0042Push00 (acc : List SourceJson) : List SourceJson := fragment0176947Value :: acc

noncomputable def chunk0042AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0042_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 431)
      (SourceJson.white (chunk0042LeadChars00 ++ (fragment0176947Chars ++ rest))) acc =
      (SourceJson.value (fuel + 430) (fragment0176947Chars ++ rest)).bind
        (chunk0042AfterValue00 (fuel + 430) acc) := by rfl

theorem array_chunk0042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 431) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 430) (SourceJson.white tail) (chunk0042Push00 acc) := by
  have hinput : chunk0042Chars00 ++ tail = chunk0042LeadChars00 ++ (fragment0176947Chars ++ (chunk0042SuffixChars00 ++ tail)) := by
    simp only [chunk0042Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 431) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 431)
          (SourceJson.white (chunk0042LeadChars00 ++ (fragment0176947Chars ++ (chunk0042SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 431) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 430) (fragment0176947Chars ++ (chunk0042SuffixChars00 ++ tail))).bind
        (chunk0042AfterValue00 (fuel + 430) acc) := array_chunk0042_head fuel (chunk0042SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0176947Value, chunk0042SuffixChars00 ++ tail)).bind
        (chunk0042AfterValue00 (fuel + 430) acc) :=
      congrArg (fun result => result.bind (chunk0042AfterValue00 (fuel + 430) acc))
        (value_fragment0176947 (fuel + 15) (chunk0042SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 430) (SourceJson.white tail) (chunk0042Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_before_reader"
  err.flush

noncomputable def chunk0043LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0043SuffixChars00 : List Char := [',']
noncomputable def chunk0043Chars00 : List Char := chunk0043LeadChars00 ++ fragment0178918Chars ++ chunk0043SuffixChars00
noncomputable def chunk0043Push00 (acc : List SourceJson) : List SourceJson := fragment0178918Value :: acc

noncomputable def chunk0043AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0043_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 430)
      (SourceJson.white (chunk0043LeadChars00 ++ (fragment0178918Chars ++ rest))) acc =
      (SourceJson.value (fuel + 429) (fragment0178918Chars ++ rest)).bind
        (chunk0043AfterValue00 (fuel + 429) acc) := by rfl

theorem array_chunk0043 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 430) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 429) (SourceJson.white tail) (chunk0043Push00 acc) := by
  have hinput : chunk0043Chars00 ++ tail = chunk0043LeadChars00 ++ (fragment0178918Chars ++ (chunk0043SuffixChars00 ++ tail)) := by
    simp only [chunk0043Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 430) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 430)
          (SourceJson.white (chunk0043LeadChars00 ++ (fragment0178918Chars ++ (chunk0043SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 430) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 429) (fragment0178918Chars ++ (chunk0043SuffixChars00 ++ tail))).bind
        (chunk0043AfterValue00 (fuel + 429) acc) := array_chunk0043_head fuel (chunk0043SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0178918Value, chunk0043SuffixChars00 ++ tail)).bind
        (chunk0043AfterValue00 (fuel + 429) acc) :=
      congrArg (fun result => result.bind (chunk0043AfterValue00 (fuel + 429) acc))
        (value_fragment0178918 (fuel + 190) (chunk0043SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 429) (SourceJson.white tail) (chunk0043Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_before_reader"
  err.flush

noncomputable def chunk0044LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0044SuffixChars00 : List Char := [',']
noncomputable def chunk0044Chars00 : List Char := chunk0044LeadChars00 ++ fragment0180516Chars ++ chunk0044SuffixChars00
noncomputable def chunk0044Push00 (acc : List SourceJson) : List SourceJson := fragment0180516Value :: acc

noncomputable def chunk0044AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0044_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 429)
      (SourceJson.white (chunk0044LeadChars00 ++ (fragment0180516Chars ++ rest))) acc =
      (SourceJson.value (fuel + 428) (fragment0180516Chars ++ rest)).bind
        (chunk0044AfterValue00 (fuel + 428) acc) := by rfl

theorem array_chunk0044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 429) (SourceJson.white (chunk0044Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 428) (SourceJson.white tail) (chunk0044Push00 acc) := by
  have hinput : chunk0044Chars00 ++ tail = chunk0044LeadChars00 ++ (fragment0180516Chars ++ (chunk0044SuffixChars00 ++ tail)) := by
    simp only [chunk0044Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 429) (SourceJson.white (chunk0044Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 429)
          (SourceJson.white (chunk0044LeadChars00 ++ (fragment0180516Chars ++ (chunk0044SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 429) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 428) (fragment0180516Chars ++ (chunk0044SuffixChars00 ++ tail))).bind
        (chunk0044AfterValue00 (fuel + 428) acc) := array_chunk0044_head fuel (chunk0044SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0180516Value, chunk0044SuffixChars00 ++ tail)).bind
        (chunk0044AfterValue00 (fuel + 428) acc) :=
      congrArg (fun result => result.bind (chunk0044AfterValue00 (fuel + 428) acc))
        (value_fragment0180516 (fuel + 169) (chunk0044SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 428) (SourceJson.white tail) (chunk0044Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_before_reader"
  err.flush

noncomputable def chunk0045LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0045SuffixChars00 : List Char := [',']
noncomputable def chunk0045Chars00 : List Char := chunk0045LeadChars00 ++ fragment0182167Chars ++ chunk0045SuffixChars00
noncomputable def chunk0045Push00 (acc : List SourceJson) : List SourceJson := fragment0182167Value :: acc

noncomputable def chunk0045AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0045_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 428)
      (SourceJson.white (chunk0045LeadChars00 ++ (fragment0182167Chars ++ rest))) acc =
      (SourceJson.value (fuel + 427) (fragment0182167Chars ++ rest)).bind
        (chunk0045AfterValue00 (fuel + 427) acc) := by rfl

theorem array_chunk0045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 428) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 427) (SourceJson.white tail) (chunk0045Push00 acc) := by
  have hinput : chunk0045Chars00 ++ tail = chunk0045LeadChars00 ++ (fragment0182167Chars ++ (chunk0045SuffixChars00 ++ tail)) := by
    simp only [chunk0045Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 428) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 428)
          (SourceJson.white (chunk0045LeadChars00 ++ (fragment0182167Chars ++ (chunk0045SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 428) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 427) (fragment0182167Chars ++ (chunk0045SuffixChars00 ++ tail))).bind
        (chunk0045AfterValue00 (fuel + 427) acc) := array_chunk0045_head fuel (chunk0045SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0182167Value, chunk0045SuffixChars00 ++ tail)).bind
        (chunk0045AfterValue00 (fuel + 427) acc) :=
      congrArg (fun result => result.bind (chunk0045AfterValue00 (fuel + 427) acc))
        (value_fragment0182167 (fuel + 166) (chunk0045SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 427) (SourceJson.white tail) (chunk0045Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_before_reader"
  err.flush

noncomputable def chunk0046LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0046SuffixChars00 : List Char := [',']
noncomputable def chunk0046Chars00 : List Char := chunk0046LeadChars00 ++ fragment0183810Chars ++ chunk0046SuffixChars00
noncomputable def chunk0046Push00 (acc : List SourceJson) : List SourceJson := fragment0183810Value :: acc

noncomputable def chunk0046AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0046_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 427)
      (SourceJson.white (chunk0046LeadChars00 ++ (fragment0183810Chars ++ rest))) acc =
      (SourceJson.value (fuel + 426) (fragment0183810Chars ++ rest)).bind
        (chunk0046AfterValue00 (fuel + 426) acc) := by rfl

theorem array_chunk0046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 427) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 426) (SourceJson.white tail) (chunk0046Push00 acc) := by
  have hinput : chunk0046Chars00 ++ tail = chunk0046LeadChars00 ++ (fragment0183810Chars ++ (chunk0046SuffixChars00 ++ tail)) := by
    simp only [chunk0046Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 427) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 427)
          (SourceJson.white (chunk0046LeadChars00 ++ (fragment0183810Chars ++ (chunk0046SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 427) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 426) (fragment0183810Chars ++ (chunk0046SuffixChars00 ++ tail))).bind
        (chunk0046AfterValue00 (fuel + 426) acc) := array_chunk0046_head fuel (chunk0046SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0183810Value, chunk0046SuffixChars00 ++ tail)).bind
        (chunk0046AfterValue00 (fuel + 426) acc) :=
      congrArg (fun result => result.bind (chunk0046AfterValue00 (fuel + 426) acc))
        (value_fragment0183810 (fuel + 143) (chunk0046SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 426) (SourceJson.white tail) (chunk0046Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_before_reader"
  err.flush

noncomputable def chunk0047LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0047SuffixChars00 : List Char := [',']
noncomputable def chunk0047Chars00 : List Char := chunk0047LeadChars00 ++ fragment0185498Chars ++ chunk0047SuffixChars00
noncomputable def chunk0047Push00 (acc : List SourceJson) : List SourceJson := fragment0185498Value :: acc

noncomputable def chunk0047AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0047_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 426)
      (SourceJson.white (chunk0047LeadChars00 ++ (fragment0185498Chars ++ rest))) acc =
      (SourceJson.value (fuel + 425) (fragment0185498Chars ++ rest)).bind
        (chunk0047AfterValue00 (fuel + 425) acc) := by rfl

theorem array_chunk0047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 426) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 425) (SourceJson.white tail) (chunk0047Push00 acc) := by
  have hinput : chunk0047Chars00 ++ tail = chunk0047LeadChars00 ++ (fragment0185498Chars ++ (chunk0047SuffixChars00 ++ tail)) := by
    simp only [chunk0047Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 426) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 426)
          (SourceJson.white (chunk0047LeadChars00 ++ (fragment0185498Chars ++ (chunk0047SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 426) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 425) (fragment0185498Chars ++ (chunk0047SuffixChars00 ++ tail))).bind
        (chunk0047AfterValue00 (fuel + 425) acc) := array_chunk0047_head fuel (chunk0047SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0185498Value, chunk0047SuffixChars00 ++ tail)).bind
        (chunk0047AfterValue00 (fuel + 425) acc) :=
      congrArg (fun result => result.bind (chunk0047AfterValue00 (fuel + 425) acc))
        (value_fragment0185498 (fuel + 174) (chunk0047SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 425) (SourceJson.white tail) (chunk0047Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0040Chars00 ++ chunk0041Chars00 ++ chunk0042Chars00 ++ chunk0043Chars00 ++ chunk0044Chars00 ++ chunk0045Chars00 ++ chunk0046Chars00 ++ chunk0047Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0047Push00 (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 433) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 425) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 433) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 433) (SourceJson.white (chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 433) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 432) (SourceJson.white (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))))) (chunk0040Push00 (acc)) := array_chunk0040 fuel (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 431) (SourceJson.white (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (chunk0041Push00 (chunk0040Push00 (acc))) := array_chunk0041 fuel (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0040Push00 (acc))
    _ = SourceJson.array (fuel + 430) (SourceJson.white (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))) := array_chunk0042 fuel (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0041Push00 (chunk0040Push00 (acc)))
    _ = SourceJson.array (fuel + 429) (SourceJson.white (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))) := array_chunk0043 fuel (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))
    _ = SourceJson.array (fuel + 428) (SourceJson.white (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))) := array_chunk0044 fuel (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))
    _ = SourceJson.array (fuel + 427) (SourceJson.white (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))) := array_chunk0045 fuel (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))
    _ = SourceJson.array (fuel + 426) (SourceJson.white (chunk0047Chars00 ++ (tail))) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))) := array_chunk0046 fuel (chunk0047Chars00 ++ (tail)) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))
    _ = SourceJson.array (fuel + 425) (SourceJson.white tail) (blockPush acc) := array_chunk0047 fuel (tail) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 173574).take 13542 = blockChars := by rfl

theorem block_original_split : sourceRest 173574 = blockChars ++ sourceRest 187116 := by
  calc
    sourceRest 173574 = (sourceRest 173574).take 13542 ++ (sourceRest 173574).drop 13542 :=
      (List.take_append_drop 13542 (sourceRest 173574)).symm
    _ = blockChars ++ (sourceRest 173574).drop 13542 :=
      congrArg (fun part => part ++ (sourceRest 173574).drop 13542) block_original_prefix
    _ = blockChars ++ sourceRest 187116 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 173574 13542)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 433) (SourceJson.white (sourceRest 173574)) acc =
      SourceJson.array (fuel + 425) (SourceJson.white (sourceRest 187116)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 433) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 187116) acc)

#print axioms object_fragment0173580_field_000
#print axioms object_fragment0173580_field_001
#print axioms object_fragment0173580_field_002
#print axioms object_fragment0173580_field_003
#print axioms object_fragment0173580_field_004
#print axioms object_fragment0173580_field_005
#print axioms object_fragment0173580_field_006
#print axioms object_fragment0173580_field_007
#print axioms object_fragment0173580_field_008
#print axioms object_fragment0173580_field_009
#print axioms value_fragment0173580
#print axioms object_fragment0175302_field_000
#print axioms object_fragment0175302_field_001
#print axioms object_fragment0175302_field_002
#print axioms object_fragment0175302_field_003
#print axioms object_fragment0175302_field_004
#print axioms object_fragment0175302_field_005
#print axioms object_fragment0175302_field_006
#print axioms object_fragment0175302_field_007
#print axioms object_fragment0175302_field_008
#print axioms object_fragment0175302_field_009
#print axioms value_fragment0175302
#print axioms object_fragment0176947_field_000
#print axioms object_fragment0176947_field_001
#print axioms object_fragment0176947_field_002
#print axioms object_fragment0176947_field_003
#print axioms object_fragment0176947_field_004
#print axioms object_fragment0176947_field_005
#print axioms object_fragment0176947_field_006
#print axioms object_fragment0176947_field_007
#print axioms object_fragment0176947_field_008
#print axioms object_fragment0176947_field_009
#print axioms value_fragment0176947
#print axioms object_fragment0178918_field_000
#print axioms object_fragment0178918_field_001
#print axioms object_fragment0178918_field_002
#print axioms object_fragment0178918_field_003
#print axioms object_fragment0178918_field_004
#print axioms object_fragment0178918_field_005
#print axioms object_fragment0178918_field_006
#print axioms object_fragment0178918_field_007
#print axioms object_fragment0178918_field_008
#print axioms object_fragment0178918_field_009
#print axioms value_fragment0178918
#print axioms object_fragment0180516_field_000
#print axioms object_fragment0180516_field_001
#print axioms object_fragment0180516_field_002
#print axioms object_fragment0180516_field_003
#print axioms object_fragment0180516_field_004
#print axioms object_fragment0180516_field_005
#print axioms object_fragment0180516_field_006
#print axioms object_fragment0180516_field_007
#print axioms object_fragment0180516_field_008
#print axioms object_fragment0180516_field_009
#print axioms value_fragment0180516
#print axioms object_fragment0182167_field_000
#print axioms object_fragment0182167_field_001
#print axioms object_fragment0182167_field_002
#print axioms object_fragment0182167_field_003
#print axioms object_fragment0182167_field_004
#print axioms object_fragment0182167_field_005
#print axioms object_fragment0182167_field_006
#print axioms object_fragment0182167_field_007
#print axioms object_fragment0182167_field_008
#print axioms object_fragment0182167_field_009
#print axioms value_fragment0182167
#print axioms object_fragment0183810_field_000
#print axioms object_fragment0183810_field_001
#print axioms object_fragment0183810_field_002
#print axioms object_fragment0183810_field_003
#print axioms object_fragment0183810_field_004
#print axioms object_fragment0183810_field_005
#print axioms object_fragment0183810_field_006
#print axioms object_fragment0183810_field_007
#print axioms object_fragment0183810_field_008
#print axioms object_fragment0183810_field_009
#print axioms value_fragment0183810
#print axioms object_fragment0185498_field_000
#print axioms object_fragment0185498_field_001
#print axioms object_fragment0185498_field_002
#print axioms object_fragment0185498_field_003
#print axioms object_fragment0185498_field_004
#print axioms object_fragment0185498_field_005
#print axioms object_fragment0185498_field_006
#print axioms object_fragment0185498_field_007
#print axioms object_fragment0185498_field_008
#print axioms object_fragment0185498_field_009
#print axioms value_fragment0185498
#print axioms array_chunk0040_head
#print axioms array_chunk0040
#print axioms array_chunk0041_head
#print axioms array_chunk0041
#print axioms array_chunk0042_head
#print axioms array_chunk0042
#print axioms array_chunk0043_head
#print axioms array_chunk0043
#print axioms array_chunk0044_head
#print axioms array_chunk0044
#print axioms array_chunk0045_head
#print axioms array_chunk0045
#print axioms array_chunk0046_head
#print axioms array_chunk0046
#print axioms array_chunk0047_head
#print axioms array_chunk0047
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock005

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
