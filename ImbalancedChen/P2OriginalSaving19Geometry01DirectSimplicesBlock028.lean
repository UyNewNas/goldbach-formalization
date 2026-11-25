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

namespace SimplicesBlock028

noncomputable def fragment0320307Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0320307Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0320307Field000Value00 : SourceJson := .number (String.ofList ['5', '5'])
noncomputable def fragment0320307Acc00100 : List (String × SourceJson) := (fragment0320307Field000Key00, fragment0320307Field000Value00) :: fragment0320307Acc00000
noncomputable def fragment0320307Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '5', ',']

theorem object_fragment0320307_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0320307Field000Chars00 ++ tail)) fragment0320307Acc00000 =
      SourceJson.object (fuel + 191) (SourceJson.white tail) fragment0320307Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_000"
  err.flush

noncomputable def fragment0320307Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0320307Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0320307Acc00200 : List (String × SourceJson) := (fragment0320307Field001Key00, fragment0320307Field001Value00) :: fragment0320307Acc00100
noncomputable def fragment0320307Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0320307_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0320307Field001Chars00 ++ tail)) fragment0320307Acc00100 =
      SourceJson.object (fuel + 190) (SourceJson.white tail) fragment0320307Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_001"
  err.flush

noncomputable def fragment0320307Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0320307Field002Value00 : SourceJson := .str (String.ofList ['6', '9', '3', '2', '5', '1', '1', '9', '8', '5', '5', '6', '3', '6', '1', '7', '7', '0', '6', '5', '7', '6', '7', '0', '7', '8', '5', '8', '3', '5', '7', '0', '8', '1', '7', '0', '1', '7', '8', '9', '/', '1', '4', '8', '3', '2', '5', '8', '3', '5', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0320307Acc00300 : List (String × SourceJson) := (fragment0320307Field002Key00, fragment0320307Field002Value00) :: fragment0320307Acc00200
noncomputable def fragment0320307Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '9', '3', '2', '5', '1', '1', '9', '8', '5', '5', '6', '3', '6', '1', '7', '7', '0', '6', '5', '7', '6', '7', '0', '7', '8', '5', '8', '3', '5', '7', '0', '8', '1', '7', '0', '1', '7', '8', '9', '/', '1', '4', '8', '3', '2', '5', '8', '3', '5', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0320307_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 190) (SourceJson.white (fragment0320307Field002Chars00 ++ tail)) fragment0320307Acc00200 =
      SourceJson.object (fuel + 189) (SourceJson.white tail) fragment0320307Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_002"
  err.flush

noncomputable def fragment0320307Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0320307Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0320307Acc00400 : List (String × SourceJson) := (fragment0320307Field003Key00, fragment0320307Field003Value00) :: fragment0320307Acc00300
noncomputable def fragment0320307Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0320307_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 189) (SourceJson.white (fragment0320307Field003Chars00 ++ tail)) fragment0320307Acc00300 =
      SourceJson.object (fuel + 188) (SourceJson.white tail) fragment0320307Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_003"
  err.flush

noncomputable def fragment0320307Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0320307Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '6', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0320307Acc00500 : List (String × SourceJson) := (fragment0320307Field004Key00, fragment0320307Field004Value00) :: fragment0320307Acc00400
noncomputable def fragment0320307Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '6', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0320307_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 188) (SourceJson.white (fragment0320307Field004Chars00 ++ tail)) fragment0320307Acc00400 =
      SourceJson.object (fuel + 187) (SourceJson.white tail) fragment0320307Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_004"
  err.flush

noncomputable def fragment0320307Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0320307Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '1', '1', '5', '8', '2', '6', '1', '/', '1', '9', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '8', '7', '5', '8', '6', '8', '3', '/', '3', '4', '9', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '0', '6', '9', '4', '0', '1', '0', '1', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '1', '7', '1', '0', '5', '3', '4', '9', '/', '1', '0', '4', '7', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '1', '6', '1', '8', '1', '8', '7', '/', '9', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '4', '7', '8', '9', '3', '4', '2', '2', '1', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '8', '0', '9', '4', '5', '5', '3', '7', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '9', '6', '9', '8', '8', '8', '5', '7', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '9', '8', '9', '9', '0', '0', '7', '9', '/', '9', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '7', '6', '0', '0', '1', '3', '2', '5', '1', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0320307Acc00600 : List (String × SourceJson) := (fragment0320307Field005Key00, fragment0320307Field005Value00) :: fragment0320307Acc00500
noncomputable def fragment0320307Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '1', '1', '5', '8', '2', '6', '1', '/', '1', '9', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '8', '7', '5', '8', '6', '8', '3', '/', '3', '4', '9', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '0', '6', '9', '4', '0', '1', '0', '1', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '1', '7', '1', '0', '5', '3', '4', '9', '/', '1', '0', '4', '7', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '1', '6', '1', '8', '1', '8', '7', '/', '9', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '7', '8', '9', '3', '4', '2', '2', '1', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '8', '0', '9', '4', '5', '5', '3', '7', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '9', '6', '9', '8', '8', '8', '5', '7', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '8', '9', '9', '0', '0', '7', '9', '/', '9', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '7', '6', '0', '0', '1', '3', '2', '5', '1', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0320307_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 187) (SourceJson.white (fragment0320307Field005Chars00 ++ tail)) fragment0320307Acc00500 =
      SourceJson.object (fuel + 186) (SourceJson.white tail) fragment0320307Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_005"
  err.flush

noncomputable def fragment0320307Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0320307Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '8', '1', '6', '6', '9', '9', '2', '7', '7', '2', '1', '3', '5', '1', '2', '7', '2', '9', '9', '8', '1', '0', '7', '9', '1', '2', '0', '4', '9', '6', '8', '3', '7', '8', '8', '6', '0', '7', '4', '8', '0', '6', '4', '0', '0', '0', '/', '1', '1', '7', '8', '5', '5', '5', '2', '0', '7', '2', '6', '8', '7', '3', '4', '9', '6', '9', '0', '1', '6', '8', '1', '2', '4', '2', '0', '7', '3', '1', '8', '5', '9', '7', '0', '1', '7', '1', '2', '1', '9', '6', '8', '7', '2', '6', '5', '7', '8', '0', '4', '7', '6', '8', '0', '5', '7', '6', '3', '2', '5', '7'])
noncomputable def fragment0320307Acc00700 : List (String × SourceJson) := (fragment0320307Field006Key00, fragment0320307Field006Value00) :: fragment0320307Acc00600
noncomputable def fragment0320307Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '8', '1', '6', '6', '9', '9', '2', '7', '7', '2', '1', '3', '5', '1', '2', '7', '2', '9', '9', '8', '1', '0', '7', '9', '1', '2', '0', '4', '9', '6', '8', '3', '7', '8', '8', '6', '0', '7', '4', '8', '0', '6', '4', '0', '0', '0', '/', '1', '1', '7', '8', '5', '5', '5', '2', '0', '7', '2', '6', '8', '7', '3', '4', '9', '6', '9', '0', '1', '6', '8', '1', '2', '4', '2', '0', '7', '3', '1', '8', '5', '9', '7', '0', '1', '7', '1', '2', '1', '9', '6', '8', '7', '2', '6', '5', '7', '8', '0', '4', '7', '6', '8', '0', '5', '7', '6', '3', '2', '5', '7', '"', ',']

theorem object_fragment0320307_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 186) (SourceJson.white (fragment0320307Field006Chars00 ++ tail)) fragment0320307Acc00600 =
      SourceJson.object (fuel + 185) (SourceJson.white tail) fragment0320307Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_006"
  err.flush

noncomputable def fragment0320307Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0320307Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '9', '5', '2', '0', '8', '2', '4', '0', '3', '8', '9', '5', '1', '9', '4', '9', '8', '3', '3', '6', '2', '9', '8', '8', '5', '0', '3', '6', '7', '8', '5', '4', '1', '5', '1', '1', '1', '9', '7', '1', '7', '3', '8', '6', '2', '4', '4', '4', '4', '0', '8', '9', '6', '8', '3', '1', '4', '3', '1', '2', '4', '4', '2', '5', '3', '5', '4', '0', '0', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '/', '8', '7', '8', '0', '4', '4', '7', '9', '5', '9', '9', '7', '4', '7', '9', '8', '9', '1', '5', '6', '4', '5', '0', '6', '6', '9', '5', '0', '9', '4', '1', '9', '0', '5', '2', '3', '0', '8', '8', '5', '9', '8', '2', '7', '0', '9', '7', '1', '4', '4', '5', '7', '7', '2', '2', '6', '7', '6', '9', '0', '8', '2', '1', '0', '5', '0', '9', '9', '3', '6', '3', '4', '6', '9', '6', '7', '1', '3', '1', '9', '8', '6', '6', '2', '2', '0', '3', '5', '8', '7', '1', '4', '9', '6', '5', '5', '7'])
noncomputable def fragment0320307Acc00800 : List (String × SourceJson) := (fragment0320307Field007Key00, fragment0320307Field007Value00) :: fragment0320307Acc00700
noncomputable def fragment0320307Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '9', '5', '2', '0', '8', '2', '4', '0', '3', '8', '9', '5', '1', '9', '4', '9', '8', '3', '3', '6', '2', '9', '8', '8', '5', '0', '3', '6', '7', '8', '5', '4', '1', '5', '1', '1', '1', '9', '7', '1', '7', '3', '8', '6', '2', '4', '4', '4', '4', '0', '8', '9', '6', '8', '3', '1', '4', '3', '1', '2', '4', '4', '2', '5', '3', '5', '4', '0', '0', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '/', '8', '7', '8', '0', '4', '4', '7', '9', '5', '9', '9', '7', '4', '7', '9', '8', '9', '1', '5', '6', '4', '5', '0', '6', '6', '9', '5', '0', '9', '4', '1', '9', '0', '5', '2', '3', '0', '8', '8', '5', '9', '8', '2', '7', '0', '9', '7', '1', '4', '4', '5', '7', '7', '2', '2', '6', '7', '6', '9', '0', '8', '2', '1', '0', '5', '0', '9', '9', '3', '6', '3', '4', '6', '9', '6', '7', '1', '3', '1', '9', '8', '6', '6', '2', '2', '0', '3', '5', '8', '7', '1', '4', '9', '6', '5', '5', '7', '"', ',']

theorem object_fragment0320307_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 185) (SourceJson.white (fragment0320307Field007Chars00 ++ tail)) fragment0320307Acc00700 =
      SourceJson.object (fuel + 184) (SourceJson.white tail) fragment0320307Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_007"
  err.flush

noncomputable def fragment0320307Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0320307Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '6', '6', '2', '3', '6', '9', '7', '5', '5', '7', '3', '1'])
noncomputable def fragment0320307Acc00900 : List (String × SourceJson) := (fragment0320307Field008Key00, fragment0320307Field008Value00) :: fragment0320307Acc00800
noncomputable def fragment0320307Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '6', '6', '6', '2', '3', '6', '9', '7', '5', '5', '7', '3', '1', '"', ',']

theorem object_fragment0320307_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 184) (SourceJson.white (fragment0320307Field008Chars00 ++ tail)) fragment0320307Acc00800 =
      SourceJson.object (fuel + 183) (SourceJson.white tail) fragment0320307Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_008"
  err.flush

noncomputable def fragment0320307Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0320307Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '9', '1', '6', '3', '5', '2', '7', '9', '0', '0', '3', '2', '4'])
noncomputable def fragment0320307Acc01000 : List (String × SourceJson) := (fragment0320307Field009Key00, fragment0320307Field009Value00) :: fragment0320307Acc00900
noncomputable def fragment0320307Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '9', '1', '6', '3', '5', '2', '7', '9', '0', '0', '3', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0320307_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 183) (SourceJson.white (fragment0320307Field009Chars00 ++ tail)) fragment0320307Acc00900 =
      .ok (.obj (fragment0320307Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320307_object_field_009"
  err.flush

noncomputable def fragment0320307Chars : List Char := '{' :: (fragment0320307Field000Chars00 ++ fragment0320307Field001Chars00 ++ fragment0320307Field002Chars00 ++ fragment0320307Field003Chars00 ++ fragment0320307Field004Chars00 ++ fragment0320307Field005Chars00 ++ fragment0320307Field006Chars00 ++ fragment0320307Field007Chars00 ++ fragment0320307Field008Chars00 ++ fragment0320307Field009Chars00)
noncomputable def fragment0320307Value : SourceJson := .obj (fragment0320307Acc01000.reverse)

theorem value_fragment0320307 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 193) (fragment0320307Chars ++ tail) =
      .ok (fragment0320307Value, tail) := by
  have hinput : fragment0320307Chars ++ tail = '{' :: (fragment0320307Field000Chars00 ++ (fragment0320307Field001Chars00 ++ (fragment0320307Field002Chars00 ++ (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0320307Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 193) (fragment0320307Chars ++ tail) =
        SourceJson.value (fuel + 193) ('{' :: (fragment0320307Field000Chars00 ++ (fragment0320307Field001Chars00 ++ (fragment0320307Field002Chars00 ++ (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 193)) hinput
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0320307Field000Chars00 ++ (fragment0320307Field001Chars00 ++ (fragment0320307Field002Chars00 ++ (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))))))))) fragment0320307Acc00000 := by rfl
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0320307Field001Chars00 ++ (fragment0320307Field002Chars00 ++ (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))))))))) fragment0320307Acc00100 := object_fragment0320307_field_000 fuel (fragment0320307Field001Chars00 ++ (fragment0320307Field002Chars00 ++ (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 190) (SourceJson.white (fragment0320307Field002Chars00 ++ (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))))))) fragment0320307Acc00200 := object_fragment0320307_field_001 fuel (fragment0320307Field002Chars00 ++ (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 189) (SourceJson.white (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))))))) fragment0320307Acc00300 := object_fragment0320307_field_002 fuel (fragment0320307Field003Chars00 ++ (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 188) (SourceJson.white (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))))) fragment0320307Acc00400 := object_fragment0320307_field_003 fuel (fragment0320307Field004Chars00 ++ (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 187) (SourceJson.white (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))))) fragment0320307Acc00500 := object_fragment0320307_field_004 fuel (fragment0320307Field005Chars00 ++ (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 186) (SourceJson.white (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))) fragment0320307Acc00600 := object_fragment0320307_field_005 fuel (fragment0320307Field006Chars00 ++ (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 185) (SourceJson.white (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))) fragment0320307Acc00700 := object_fragment0320307_field_006 fuel (fragment0320307Field007Chars00 ++ (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 184) (SourceJson.white (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))) fragment0320307Acc00800 := object_fragment0320307_field_007 fuel (fragment0320307Field008Chars00 ++ (fragment0320307Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 183) (SourceJson.white (fragment0320307Field009Chars00 ++ (tail))) fragment0320307Acc00900 := object_fragment0320307_field_008 fuel (fragment0320307Field009Chars00 ++ (tail))
    _ = .ok (fragment0320307Value, tail) := object_fragment0320307_field_009 fuel (tail)

noncomputable def fragment0321829Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0321829Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0321829Field000Value00 : SourceJson := .number (String.ofList ['5', '6'])
noncomputable def fragment0321829Acc00100 : List (String × SourceJson) := (fragment0321829Field000Key00, fragment0321829Field000Value00) :: fragment0321829Acc00000
noncomputable def fragment0321829Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '6', ',']

theorem object_fragment0321829_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 389) (SourceJson.white (fragment0321829Field000Chars00 ++ tail)) fragment0321829Acc00000 =
      SourceJson.object (fuel + 388) (SourceJson.white tail) fragment0321829Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_000"
  err.flush

noncomputable def fragment0321829Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0321829Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0321829Acc00200 : List (String × SourceJson) := (fragment0321829Field001Key00, fragment0321829Field001Value00) :: fragment0321829Acc00100
noncomputable def fragment0321829Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0321829_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 388) (SourceJson.white (fragment0321829Field001Chars00 ++ tail)) fragment0321829Acc00100 =
      SourceJson.object (fuel + 387) (SourceJson.white tail) fragment0321829Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_001"
  err.flush

noncomputable def fragment0321829Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0321829Field002Value00 : SourceJson := .str (String.ofList ['1', '6', '3', '6', '5', '4', '6', '3', '9', '0', '5', '1', '6', '6', '3', '6', '4', '0', '3', '5', '6', '4', '7', '0', '6', '9', '7', '0', '2', '0', '5', '2', '1', '3', '3', '1', '8', '5', '7', '2', '3', '0', '7', '/', '1', '5', '9', '0', '4', '7', '6', '7', '4', '5', '4', '2', '4', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0321829Acc00300 : List (String × SourceJson) := (fragment0321829Field002Key00, fragment0321829Field002Value00) :: fragment0321829Acc00200
noncomputable def fragment0321829Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '6', '3', '6', '5', '4', '6', '3', '9', '0', '5', '1', '6', '6', '3', '6', '4', '0', '3', '5', '6', '4', '7', '0', '6', '9', '7', '0', '2', '0', '5', '2', '1', '3', '3', '1', '8', '5', '7', '2', '3', '0', '7', '/', '1', '5', '9', '0', '4', '7', '6', '7', '4', '5', '4', '2', '4', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0321829_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 387) (SourceJson.white (fragment0321829Field002Chars00 ++ tail)) fragment0321829Acc00200 =
      SourceJson.object (fuel + 386) (SourceJson.white tail) fragment0321829Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_002"
  err.flush

noncomputable def fragment0321829Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0321829Field003Value00 : SourceJson := .str (String.ofList ['3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0'])
noncomputable def fragment0321829Acc00400 : List (String × SourceJson) := (fragment0321829Field003Key00, fragment0321829Field003Value00) :: fragment0321829Acc00300
noncomputable def fragment0321829Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0321829_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 386) (SourceJson.white (fragment0321829Field003Chars00 ++ tail)) fragment0321829Acc00300 =
      SourceJson.object (fuel + 385) (SourceJson.white tail) fragment0321829Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_003"
  err.flush

noncomputable def fragment0321829Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0321829Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['8', '0', '7', '/', '1', '7', '7', '9', '2'])]
noncomputable def fragment0321829Acc00500 : List (String × SourceJson) := (fragment0321829Field004Key00, fragment0321829Field004Value00) :: fragment0321829Acc00400
noncomputable def fragment0321829Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '/', '1', '7', '7', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0321829_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 385) (SourceJson.white (fragment0321829Field004Chars00 ++ tail)) fragment0321829Acc00400 =
      SourceJson.object (fuel + 384) (SourceJson.white tail) fragment0321829Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_004"
  err.flush

noncomputable def fragment0321829Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0321829Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '2', '5', '2', '5', '9', '0', '9', '2', '6', '8', '8', '6', '9', '8', '7', '2', '7', '3', '/', '1', '9', '2', '0', '6', '1', '7', '8', '1', '3', '1', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '1', '1', '6', '6', '7', '6', '1', '7', '9', '1', '3', '8', '5', '6', '6', '0', '3', '9', '/', '6', '7', '2', '2', '1', '6', '2', '3', '4', '5', '9', '2', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '6', '8', '3', '7', '2', '9', '2', '2', '0', '6', '1', '7', '6', '5', '9', '2', '8', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '3', '9', '5', '1', '9', '5', '1', '5', '7', '1', '9', '9', '8', '5', '2', '0', '3', '/', '1', '2', '6', '0', '4', '0', '5', '4', '3', '9', '8', '6', '0', '6', '5', '6', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '9', '7', '7', '6', '8', '7', '3', '8', '7', '5', '6', '9', '5', '0', '2', '3', '1', '4', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '6', '3', '8', '6', '7', '9', '1', '1', '8', '4', '0', '2', '7', '3', '7', '7', '6', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '3', '1', '2', '4', '9', '5', '4', '0', '0', '5', '6', '4', '3', '7', '5', '7', '0', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '8', '7', '6', '6', '1', '5', '5', '7', '8', '2', '8', '7', '1', '1', '4', '2', '9', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '6', '2', '5', '5', '0', '8', '6', '4', '9', '8', '1', '8', '6', '1', '1', '7', '7', '1', '/', '4', '4', '8', '1', '4', '4', '1', '5', '6', '3', '9', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '1', '9', '2', '0', '6', '6', '2', '2', '8', '6', '2', '2', '2', '7', '9', '5', '2', '6', '1', '/', '8', '0', '6', '6', '5', '9', '4', '8', '1', '5', '1', '0', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0321829Acc00600 : List (String × SourceJson) := (fragment0321829Field005Key00, fragment0321829Field005Value00) :: fragment0321829Acc00500
noncomputable def fragment0321829Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '5', '2', '5', '9', '0', '9', '2', '6', '8', '8', '6', '9', '8', '7', '2', '7', '3', '/', '1', '9', '2', '0', '6', '1', '7', '8', '1', '3', '1', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '1', '1', '6', '6', '7', '6', '1', '7', '9', '1', '3', '8', '5', '6', '6', '0', '3', '9', '/', '6', '7', '2', '2', '1', '6', '2', '3', '4', '5', '9', '2', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '6', '8', '3', '7', '2', '9', '2', '2', '0', '6', '1', '7', '6', '5', '9', '2', '8', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '3', '9', '5', '1', '9', '5', '1', '5', '7', '1', '9', '9', '8', '5', '2', '0', '3', '/', '1', '2', '6', '0', '4', '0', '5', '4', '3', '9', '8', '6', '0', '6', '5', '6', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '7', '6', '8', '7', '3', '8', '7', '5', '6', '9', '5', '0', '2', '3', '1', '4', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '6', '3', '8', '6', '7', '9', '1', '1', '8', '4', '0', '2', '7', '3', '7', '7', '6', '3', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '3', '1', '2', '4', '9', '5', '4', '0', '0', '5', '6', '4', '3', '7', '5', '7', '0', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '8', '7', '6', '6', '1', '5', '5', '7', '8', '2', '8', '7', '1', '1', '4', '2', '9', '3', '/', '1', '3', '4', '4', '4', '3', '2', '4', '6', '9', '1', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '2', '5', '5', '0', '8', '6', '4', '9', '8', '1', '8', '6', '1', '1', '7', '7', '1', '/', '4', '4', '8', '1', '4', '4', '1', '5', '6', '3', '9', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '9', '2', '0', '6', '6', '2', '2', '8', '6', '2', '2', '2', '7', '9', '5', '2', '6', '1', '/', '8', '0', '6', '6', '5', '9', '4', '8', '1', '5', '1', '0', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0321829_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 384) (SourceJson.white (fragment0321829Field005Chars00 ++ tail)) fragment0321829Acc00500 =
      SourceJson.object (fuel + 383) (SourceJson.white tail) fragment0321829Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_005"
  err.flush

noncomputable def fragment0321829Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0321829Field006Value00 : SourceJson := .str (String.ofList ['7', '8', '7', '7', '6', '4', '4', '4', '8', '5', '2', '7', '6', '0', '1', '0', '6', '8', '3', '6', '6', '7', '0', '3', '2', '3', '5', '5', '7', '2', '1', '1', '0', '9', '0', '4', '3', '8', '8', '3', '8', '2', '7', '9', '8', '0', '5', '8', '1', '0', '5', '3', '/', '1', '5', '6', '2', '4', '3', '1', '7', '1', '9', '1', '5', '3', '5', '5', '7', '7', '6', '8', '9', '2', '2', '1', '6', '5', '7', '5', '6', '4', '1', '8', '7', '0', '3', '2', '7', '2', '2', '1', '4', '0', '5', '2', '5', '1', '2', '3', '4', '9', '4', '5', '6', '2', '5', '2', '9', '6', '0', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0'])
noncomputable def fragment0321829Acc00700 : List (String × SourceJson) := (fragment0321829Field006Key00, fragment0321829Field006Value00) :: fragment0321829Acc00600
noncomputable def fragment0321829Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '8', '7', '7', '6', '4', '4', '4', '8', '5', '2', '7', '6', '0', '1', '0', '6', '8', '3', '6', '6', '7', '0', '3', '2', '3', '5', '5', '7', '2', '1', '1', '0', '9', '0', '4', '3', '8', '8', '3', '8', '2', '7', '9', '8', '0', '5', '8', '1', '0', '5', '3', '/', '1', '5', '6', '2', '4', '3', '1', '7', '1', '9', '1', '5', '3', '5', '5', '7', '7', '6', '8', '9', '2', '2', '1', '6', '5', '7', '5', '6', '4', '1', '8', '7', '0', '3', '2', '7', '2', '2', '1', '4', '0', '5', '2', '5', '1', '2', '3', '4', '9', '4', '5', '6', '2', '5', '2', '9', '6', '0', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0', '"', ',']

theorem object_fragment0321829_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 383) (SourceJson.white (fragment0321829Field006Chars00 ++ tail)) fragment0321829Acc00600 =
      SourceJson.object (fuel + 382) (SourceJson.white tail) fragment0321829Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_006"
  err.flush

noncomputable def fragment0321829Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0321829Field007Value00 : SourceJson := .str (String.ofList ['3', '4', '5', '2', '8', '2', '6', '5', '9', '6', '2', '5', '8', '0', '7', '2', '1', '0', '9', '8', '1', '8', '6', '7', '6', '6', '9', '5', '7', '3', '9', '7', '9', '7', '6', '6', '7', '4', '5', '8', '3', '1', '0', '7', '4', '8', '7', '2', '4', '9', '8', '6', '6', '0', '9', '0', '4', '1', '3', '3', '2', '1', '4', '0', '5', '0', '1', '7', '2', '2', '3', '9', '0', '1', '3', '2', '3', '3', '6', '2', '2', '9', '2', '4', '2', '0', '6', '2', '6', '7', '4', '0', '0', '6', '7', '6', '5', '5', '7', '9', '6', '6', '9', '6', '6', '5', '6', '3', '0', '6', '8', '2', '2', '0', '1', '3', '6', '5', '3', '4', '5', '6', '6', '6', '6', '6', '4', '1', '1', '0', '8', '5', '5', '6', '3', '9', '0', '8', '9', '2', '4', '1', '0', '9', '7', '8', '2', '6', '5', '3', '1', '4', '5', '7', '3', '0', '8', '8', '2', '1', '0', '3', '3', '8', '5', '9', '2', '5', '2', '9', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '7', '8', '1', '8', '9', '9', '7', '8', '1', '4', '2', '3', '1', '2', '1', '5', '0', '8', '1', '6', '5', '3', '7', '2', '7', '4', '8', '1', '2', '1', '6', '9', '4', '2', '4', '8', '0', '6', '9', '9', '3', '1', '4', '0', '6', '0', '3', '4', '5', '3', '9', '0', '1', '2', '4', '8', '4', '8', '3', '3', '2', '4', '6', '8', '3', '7', '2', '8', '5', '7', '9', '8', '4', '8', '9', '5', '9', '9', '1', '4', '4', '5', '2', '5', '9', '1', '1', '2', '5', '1', '6', '8', '2', '8', '2', '2', '1', '0', '0', '2', '8', '4', '2', '2', '2', '4', '2', '1', '2', '0', '7', '4', '5', '3', '1', '3', '8', '0', '5', '6', '2', '4', '3', '5', '7', '5', '7', '5', '1', '8', '0', '5', '6', '8', '5', '4', '7', '3', '5', '6', '9', '3', '3', '8', '7', '4', '0', '5', '0', '4', '3', '3', '9', '5', '5', '3', '1', '6', '7', '1', '5', '2', '4', '2', '4', '2', '9', '1', '0', '4', '4', '3', '5', '6', '5', '3', '1', '3', '8', '5', '1', '4', '7', '7', '0', '7', '3', '0', '6', '0', '9', '6', '0', '1', '2', '9'])
noncomputable def fragment0321829Acc00800 : List (String × SourceJson) := (fragment0321829Field007Key00, fragment0321829Field007Value00) :: fragment0321829Acc00700
noncomputable def fragment0321829Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '5', '2', '8', '2', '6', '5', '9', '6', '2', '5', '8', '0', '7', '2', '1', '0', '9', '8', '1', '8', '6', '7', '6', '6', '9', '5', '7', '3', '9', '7', '9', '7', '6', '6', '7', '4', '5', '8', '3', '1', '0', '7', '4', '8', '7', '2', '4', '9', '8', '6', '6', '0', '9', '0', '4', '1', '3', '3', '2', '1', '4', '0', '5', '0', '1', '7', '2', '2', '3', '9', '0', '1', '3', '2', '3', '3', '6', '2', '2', '9', '2', '4', '2', '0', '6', '2', '6', '7', '4', '0', '0', '6', '7', '6', '5', '5', '7', '9', '6', '6', '9', '6', '6', '5', '6', '3', '0', '6', '8', '2', '2', '0', '1', '3', '6', '5', '3', '4', '5', '6', '6', '6', '6', '6', '4', '1', '1', '0', '8', '5', '5', '6', '3', '9', '0', '8', '9', '2', '4', '1', '0', '9', '7', '8', '2', '6', '5', '3', '1', '4', '5', '7', '3', '0', '8', '8', '2', '1', '0', '3', '3', '8', '5', '9', '2', '5', '2', '9', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '7', '8', '1', '8', '9', '9', '7', '8', '1', '4', '2', '3', '1', '2', '1', '5', '0', '8', '1', '6', '5', '3', '7', '2', '7', '4', '8', '1', '2', '1', '6', '9', '4', '2', '4', '8', '0', '6', '9', '9', '3', '1', '4', '0', '6', '0', '3', '4', '5', '3', '9', '0', '1', '2', '4', '8', '4', '8', '3', '3', '2', '4', '6', '8', '3', '7', '2', '8', '5', '7', '9', '8', '4', '8', '9', '5', '9', '9', '1', '4', '4', '5', '2', '5', '9', '1', '1', '2', '5', '1', '6', '8', '2', '8', '2', '2', '1', '0', '0', '2', '8', '4', '2', '2', '2', '4', '2', '1', '2', '0', '7', '4', '5', '3', '1', '3', '8', '0', '5', '6', '2', '4', '3', '5', '7', '5', '7', '5', '1', '8', '0', '5', '6', '8', '5', '4', '7', '3', '5', '6', '9', '3', '3', '8', '7', '4', '0', '5', '0', '4', '3', '3', '9', '5', '5', '3', '1', '6', '7', '1', '5', '2', '4', '2', '4', '2', '9', '1', '0', '4', '4', '3', '5', '6', '5', '3', '1', '3', '8', '5', '1', '4', '7', '7', '0', '7', '3', '0', '6', '0', '9', '6', '0', '1', '2', '9', '"', ',']

theorem object_fragment0321829_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 382) (SourceJson.white (fragment0321829Field007Chars00 ++ tail)) fragment0321829Acc00700 =
      SourceJson.object (fuel + 381) (SourceJson.white tail) fragment0321829Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_007"
  err.flush

noncomputable def fragment0321829Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0321829Field008Value00 : SourceJson := .str (String.ofList ['3', '9', '9', '4', '6', '1', '4', '8', '6', '7', '6', '9', '5', '8'])
noncomputable def fragment0321829Acc00900 : List (String × SourceJson) := (fragment0321829Field008Key00, fragment0321829Field008Value00) :: fragment0321829Acc00800
noncomputable def fragment0321829Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '9', '4', '6', '1', '4', '8', '6', '7', '6', '9', '5', '8', '"', ',']

theorem object_fragment0321829_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 381) (SourceJson.white (fragment0321829Field008Chars00 ++ tail)) fragment0321829Acc00800 =
      SourceJson.object (fuel + 380) (SourceJson.white tail) fragment0321829Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_008"
  err.flush

noncomputable def fragment0321829Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0321829Field009Value00 : SourceJson := .str (String.ofList ['3', '4', '9', '8', '6', '7', '2', '2', '4', '9', '3', '2', '5', '9', '3'])
noncomputable def fragment0321829Acc01000 : List (String × SourceJson) := (fragment0321829Field009Key00, fragment0321829Field009Value00) :: fragment0321829Acc00900
noncomputable def fragment0321829Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '9', '8', '6', '7', '2', '2', '4', '9', '3', '2', '5', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0321829_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 380) (SourceJson.white (fragment0321829Field009Chars00 ++ tail)) fragment0321829Acc00900 =
      .ok (.obj (fragment0321829Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0321829_object_field_009"
  err.flush

noncomputable def fragment0321829Chars : List Char := '{' :: (fragment0321829Field000Chars00 ++ fragment0321829Field001Chars00 ++ fragment0321829Field002Chars00 ++ fragment0321829Field003Chars00 ++ fragment0321829Field004Chars00 ++ fragment0321829Field005Chars00 ++ fragment0321829Field006Chars00 ++ fragment0321829Field007Chars00 ++ fragment0321829Field008Chars00 ++ fragment0321829Field009Chars00)
noncomputable def fragment0321829Value : SourceJson := .obj (fragment0321829Acc01000.reverse)

theorem value_fragment0321829 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 390) (fragment0321829Chars ++ tail) =
      .ok (fragment0321829Value, tail) := by
  have hinput : fragment0321829Chars ++ tail = '{' :: (fragment0321829Field000Chars00 ++ (fragment0321829Field001Chars00 ++ (fragment0321829Field002Chars00 ++ (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0321829Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 390) (fragment0321829Chars ++ tail) =
        SourceJson.value (fuel + 390) ('{' :: (fragment0321829Field000Chars00 ++ (fragment0321829Field001Chars00 ++ (fragment0321829Field002Chars00 ++ (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 390)) hinput
    _ = SourceJson.object (fuel + 389) (SourceJson.white (fragment0321829Field000Chars00 ++ (fragment0321829Field001Chars00 ++ (fragment0321829Field002Chars00 ++ (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))))))))) fragment0321829Acc00000 := by rfl
    _ = SourceJson.object (fuel + 388) (SourceJson.white (fragment0321829Field001Chars00 ++ (fragment0321829Field002Chars00 ++ (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))))))))) fragment0321829Acc00100 := object_fragment0321829_field_000 fuel (fragment0321829Field001Chars00 ++ (fragment0321829Field002Chars00 ++ (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 387) (SourceJson.white (fragment0321829Field002Chars00 ++ (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))))))) fragment0321829Acc00200 := object_fragment0321829_field_001 fuel (fragment0321829Field002Chars00 ++ (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 386) (SourceJson.white (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))))))) fragment0321829Acc00300 := object_fragment0321829_field_002 fuel (fragment0321829Field003Chars00 ++ (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 385) (SourceJson.white (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))))) fragment0321829Acc00400 := object_fragment0321829_field_003 fuel (fragment0321829Field004Chars00 ++ (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 384) (SourceJson.white (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))))) fragment0321829Acc00500 := object_fragment0321829_field_004 fuel (fragment0321829Field005Chars00 ++ (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 383) (SourceJson.white (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))) fragment0321829Acc00600 := object_fragment0321829_field_005 fuel (fragment0321829Field006Chars00 ++ (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 382) (SourceJson.white (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))) fragment0321829Acc00700 := object_fragment0321829_field_006 fuel (fragment0321829Field007Chars00 ++ (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 381) (SourceJson.white (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))) fragment0321829Acc00800 := object_fragment0321829_field_007 fuel (fragment0321829Field008Chars00 ++ (fragment0321829Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 380) (SourceJson.white (fragment0321829Field009Chars00 ++ (tail))) fragment0321829Acc00900 := object_fragment0321829_field_008 fuel (fragment0321829Field009Chars00 ++ (tail))
    _ = .ok (fragment0321829Value, tail) := object_fragment0321829_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_before_reader"
  err.flush

noncomputable def chunk0055LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0055SuffixChars00 : List Char := [',']
noncomputable def chunk0055Chars00 : List Char := chunk0055LeadChars00 ++ fragment0320307Chars ++ chunk0055SuffixChars00
noncomputable def chunk0055Push00 (acc : List SourceJson) : List SourceJson := fragment0320307Value :: acc

noncomputable def chunk0055AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0055_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 549)
      (SourceJson.white (chunk0055LeadChars00 ++ (fragment0320307Chars ++ rest))) acc =
      (SourceJson.value (fuel + 548) (fragment0320307Chars ++ rest)).bind
        (chunk0055AfterValue00 (fuel + 548) acc) := by rfl

theorem array_chunk0055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 549) (SourceJson.white (chunk0055Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 548) (SourceJson.white tail) (chunk0055Push00 acc) := by
  have hinput : chunk0055Chars00 ++ tail = chunk0055LeadChars00 ++ (fragment0320307Chars ++ (chunk0055SuffixChars00 ++ tail)) := by
    simp only [chunk0055Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 549) (SourceJson.white (chunk0055Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 549)
          (SourceJson.white (chunk0055LeadChars00 ++ (fragment0320307Chars ++ (chunk0055SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 549) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 548) (fragment0320307Chars ++ (chunk0055SuffixChars00 ++ tail))).bind
        (chunk0055AfterValue00 (fuel + 548) acc) := array_chunk0055_head fuel (chunk0055SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0320307Value, chunk0055SuffixChars00 ++ tail)).bind
        (chunk0055AfterValue00 (fuel + 548) acc) :=
      congrArg (fun result => result.bind (chunk0055AfterValue00 (fuel + 548) acc))
        (value_fragment0320307 (fuel + 355) (chunk0055SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 548) (SourceJson.white tail) (chunk0055Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0056_before_reader"
  err.flush

noncomputable def chunk0056LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0056SuffixChars00 : List Char := [',']
noncomputable def chunk0056Chars00 : List Char := chunk0056LeadChars00 ++ fragment0321829Chars ++ chunk0056SuffixChars00
noncomputable def chunk0056Push00 (acc : List SourceJson) : List SourceJson := fragment0321829Value :: acc

noncomputable def chunk0056AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0056_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 548)
      (SourceJson.white (chunk0056LeadChars00 ++ (fragment0321829Chars ++ rest))) acc =
      (SourceJson.value (fuel + 547) (fragment0321829Chars ++ rest)).bind
        (chunk0056AfterValue00 (fuel + 547) acc) := by rfl

theorem array_chunk0056 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 548) (SourceJson.white (chunk0056Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 547) (SourceJson.white tail) (chunk0056Push00 acc) := by
  have hinput : chunk0056Chars00 ++ tail = chunk0056LeadChars00 ++ (fragment0321829Chars ++ (chunk0056SuffixChars00 ++ tail)) := by
    simp only [chunk0056Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 548) (SourceJson.white (chunk0056Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 548)
          (SourceJson.white (chunk0056LeadChars00 ++ (fragment0321829Chars ++ (chunk0056SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 548) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 547) (fragment0321829Chars ++ (chunk0056SuffixChars00 ++ tail))).bind
        (chunk0056AfterValue00 (fuel + 547) acc) := array_chunk0056_head fuel (chunk0056SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0321829Value, chunk0056SuffixChars00 ++ tail)).bind
        (chunk0056AfterValue00 (fuel + 547) acc) :=
      congrArg (fun result => result.bind (chunk0056AfterValue00 (fuel + 547) acc))
        (value_fragment0321829 (fuel + 157) (chunk0056SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 547) (SourceJson.white tail) (chunk0056Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0056_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0055Chars00 ++ chunk0056Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0056Push00 (chunk0055Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 549) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 547) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0055Chars00 ++ (chunk0056Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 549) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 549) (SourceJson.white (chunk0055Chars00 ++ (chunk0056Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 549) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 548) (SourceJson.white (chunk0056Chars00 ++ (tail))) (chunk0055Push00 (acc)) := array_chunk0055 fuel (chunk0056Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 547) (SourceJson.white tail) (blockPush acc) := array_chunk0056 fuel (tail) (chunk0055Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 320301).take 3430 = blockChars := by rfl

theorem block_original_split : sourceRest 320301 = blockChars ++ sourceRest 323731 := by
  calc
    sourceRest 320301 = (sourceRest 320301).take 3430 ++ (sourceRest 320301).drop 3430 :=
      (List.take_append_drop 3430 (sourceRest 320301)).symm
    _ = blockChars ++ (sourceRest 320301).drop 3430 :=
      congrArg (fun part => part ++ (sourceRest 320301).drop 3430) block_original_prefix
    _ = blockChars ++ sourceRest 323731 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 320301 3430)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 549) (SourceJson.white (sourceRest 320301)) acc =
      SourceJson.array (fuel + 547) (SourceJson.white (sourceRest 323731)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 549) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 323731) acc)

#print axioms object_fragment0320307_field_000
#print axioms object_fragment0320307_field_001
#print axioms object_fragment0320307_field_002
#print axioms object_fragment0320307_field_003
#print axioms object_fragment0320307_field_004
#print axioms object_fragment0320307_field_005
#print axioms object_fragment0320307_field_006
#print axioms object_fragment0320307_field_007
#print axioms object_fragment0320307_field_008
#print axioms object_fragment0320307_field_009
#print axioms value_fragment0320307
#print axioms object_fragment0321829_field_000
#print axioms object_fragment0321829_field_001
#print axioms object_fragment0321829_field_002
#print axioms object_fragment0321829_field_003
#print axioms object_fragment0321829_field_004
#print axioms object_fragment0321829_field_005
#print axioms object_fragment0321829_field_006
#print axioms object_fragment0321829_field_007
#print axioms object_fragment0321829_field_008
#print axioms object_fragment0321829_field_009
#print axioms value_fragment0321829
#print axioms array_chunk0055_head
#print axioms array_chunk0055
#print axioms array_chunk0056_head
#print axioms array_chunk0056
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock028

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
