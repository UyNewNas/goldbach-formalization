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

namespace SimplicesBlock063

noncomputable def fragment0437352Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0437352Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0437352Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '4'])
noncomputable def fragment0437352Acc00100 : List (String × SourceJson) := (fragment0437352Field000Key00, fragment0437352Field000Value00) :: fragment0437352Acc00000
noncomputable def fragment0437352Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '4', ',']

theorem object_fragment0437352_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0437352Field000Chars00 ++ tail)) fragment0437352Acc00000 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0437352Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_000"
  err.flush

noncomputable def fragment0437352Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0437352Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0437352Acc00200 : List (String × SourceJson) := (fragment0437352Field001Key00, fragment0437352Field001Value00) :: fragment0437352Acc00100
noncomputable def fragment0437352Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0437352_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0437352Field001Chars00 ++ tail)) fragment0437352Acc00100 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0437352Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_001"
  err.flush

noncomputable def fragment0437352Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0437352Field002Value00 : SourceJson := .str (String.ofList ['2', '4', '6', '7', '7', '9', '7', '3', '8', '8', '8', '5', '4', '8', '8', '8', '5', '8', '7', '8', '2', '4', '2', '5', '8', '2', '2', '7', '8', '1', '8', '2', '2', '1', '7', '/', '7', '1', '4', '4', '2', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0437352Acc00300 : List (String × SourceJson) := (fragment0437352Field002Key00, fragment0437352Field002Value00) :: fragment0437352Acc00200
noncomputable def fragment0437352Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '4', '6', '7', '7', '9', '7', '3', '8', '8', '8', '5', '4', '8', '8', '8', '5', '8', '7', '8', '2', '4', '2', '5', '8', '2', '2', '7', '8', '1', '8', '2', '2', '1', '7', '/', '7', '1', '4', '4', '2', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0437352_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0437352Field002Chars00 ++ tail)) fragment0437352Acc00200 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0437352Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_002"
  err.flush

noncomputable def fragment0437352Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0437352Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0437352Acc00400 : List (String × SourceJson) := (fragment0437352Field003Key00, fragment0437352Field003Value00) :: fragment0437352Acc00300
noncomputable def fragment0437352Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0437352_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0437352Field003Chars00 ++ tail)) fragment0437352Acc00300 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0437352Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_003"
  err.flush

noncomputable def fragment0437352Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0437352Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0437352Acc00500 : List (String × SourceJson) := (fragment0437352Field004Key00, fragment0437352Field004Value00) :: fragment0437352Acc00400
noncomputable def fragment0437352Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0437352_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0437352Field004Chars00 ++ tail)) fragment0437352Acc00400 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0437352Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_004"
  err.flush

noncomputable def fragment0437352Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0437352Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '3', '5', '1', '1', '6', '0', '1', '5', '2', '6', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '0', '2', '0', '9', '4', '4', '1', '7', '8', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '4', '3', '8', '1', '4', '6', '8', '1', '1', '/', '3', '8', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '3', '5', '6', '2', '6', '6', '1', '9', '3', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '9', '3', '0', '0', '8', '7', '9', '/', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '9', '1', '7', '4', '6', '8', '4', '7', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '8', '8', '2', '9', '5', '8', '7', '9', '/', '1', '6', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '0', '4', '5', '8', '1', '8', '5', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '1', '8', '0', '6', '4', '2', '7', '1', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '3', '9', '3', '4', '3', '5', '5', '9', '9', '/', '1', '6', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0437352Acc00600 : List (String × SourceJson) := (fragment0437352Field005Key00, fragment0437352Field005Value00) :: fragment0437352Acc00500
noncomputable def fragment0437352Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '5', '1', '1', '6', '0', '1', '5', '2', '6', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '0', '2', '0', '9', '4', '4', '1', '7', '8', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '3', '8', '1', '4', '6', '8', '1', '1', '/', '3', '8', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '3', '5', '6', '2', '6', '6', '1', '9', '3', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '6', '9', '3', '0', '0', '8', '7', '9', '/', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '9', '1', '7', '4', '6', '8', '4', '7', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '8', '8', '2', '9', '5', '8', '7', '9', '/', '1', '6', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '0', '4', '5', '8', '1', '8', '5', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '1', '8', '0', '6', '4', '2', '7', '1', '7', '/', '5', '0', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '9', '3', '4', '3', '5', '5', '9', '9', '/', '1', '6', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0437352_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0437352Field005Chars00 ++ tail)) fragment0437352Acc00500 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0437352Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_005"
  err.flush

noncomputable def fragment0437352Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0437352Field006Value00 : SourceJson := .str (String.ofList ['6', '8', '5', '1', '6', '0', '7', '6', '3', '5', '9', '6', '8', '4', '3', '0', '2', '6', '2', '3', '6', '3', '8', '2', '5', '5', '1', '7', '1', '1', '8', '2', '5', '3', '1', '3', '3', '2', '0', '7', '6', '8', '0', '0', '0', '/', '5', '2', '1', '2', '5', '7', '9', '6', '9', '6', '8', '9', '4', '5', '4', '1', '5', '7', '8', '8', '9', '0', '2', '5', '4', '0', '6', '9', '2', '2', '5', '9', '9', '6', '4', '2', '1', '8', '3', '7', '5', '7', '9', '4', '3', '8', '1', '1', '9', '7', '3', '6', '0', '2', '2', '0', '8', '9', '9', '7'])
noncomputable def fragment0437352Acc00700 : List (String × SourceJson) := (fragment0437352Field006Key00, fragment0437352Field006Value00) :: fragment0437352Acc00600
noncomputable def fragment0437352Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '8', '5', '1', '6', '0', '7', '6', '3', '5', '9', '6', '8', '4', '3', '0', '2', '6', '2', '3', '6', '3', '8', '2', '5', '5', '1', '7', '1', '1', '8', '2', '5', '3', '1', '3', '3', '2', '0', '7', '6', '8', '0', '0', '0', '/', '5', '2', '1', '2', '5', '7', '9', '6', '9', '6', '8', '9', '4', '5', '4', '1', '5', '7', '8', '8', '9', '0', '2', '5', '4', '0', '6', '9', '2', '2', '5', '9', '9', '6', '4', '2', '1', '8', '3', '7', '5', '7', '9', '4', '3', '8', '1', '1', '9', '7', '3', '6', '0', '2', '2', '0', '8', '9', '9', '7', '"', ',']

theorem object_fragment0437352_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0437352Field006Chars00 ++ tail)) fragment0437352Acc00600 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0437352Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_006"
  err.flush

noncomputable def fragment0437352Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0437352Field007Value00 : SourceJson := .str (String.ofList ['6', '2', '3', '6', '1', '4', '4', '4', '9', '0', '8', '7', '8', '3', '7', '0', '0', '1', '9', '5', '6', '0', '1', '0', '6', '9', '9', '2', '8', '8', '7', '5', '0', '3', '4', '2', '9', '9', '2', '7', '5', '3', '8', '3', '5', '7', '7', '6', '8', '9', '9', '2', '1', '5', '1', '1', '2', '2', '8', '2', '9', '1', '2', '9', '9', '7', '6', '3', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '1', '3', '4', '4', '9', '9', '6', '9', '4', '3', '8', '7', '0', '0', '1', '5', '8', '0', '8', '6', '4', '9', '1', '9', '3', '3', '4', '6', '8', '2', '8', '0', '3', '4', '3', '6', '6', '9', '1', '7', '8', '5', '7', '3', '7', '1', '7', '7', '1', '6', '5', '5', '6', '4', '5', '7', '9', '4', '4', '9', '3', '9', '1', '4', '0', '8', '9', '0', '6', '2', '8', '5', '8', '3', '4', '8', '9', '7', '7', '1', '8', '5', '9', '7', '0', '6', '1', '9', '4', '0', '5', '9', '9', '6', '1', '0', '0', '4', '6', '0', '3', '6', '9', '2', '9', '1', '9', '9'])
noncomputable def fragment0437352Acc00800 : List (String × SourceJson) := (fragment0437352Field007Key00, fragment0437352Field007Value00) :: fragment0437352Acc00700
noncomputable def fragment0437352Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '2', '3', '6', '1', '4', '4', '4', '9', '0', '8', '7', '8', '3', '7', '0', '0', '1', '9', '5', '6', '0', '1', '0', '6', '9', '9', '2', '8', '8', '7', '5', '0', '3', '4', '2', '9', '9', '2', '7', '5', '3', '8', '3', '5', '7', '7', '6', '8', '9', '9', '2', '1', '5', '1', '1', '2', '2', '8', '2', '9', '1', '2', '9', '9', '7', '6', '3', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '1', '3', '4', '4', '9', '9', '6', '9', '4', '3', '8', '7', '0', '0', '1', '5', '8', '0', '8', '6', '4', '9', '1', '9', '3', '3', '4', '6', '8', '2', '8', '0', '3', '4', '3', '6', '6', '9', '1', '7', '8', '5', '7', '3', '7', '1', '7', '7', '1', '6', '5', '5', '6', '4', '5', '7', '9', '4', '4', '9', '3', '9', '1', '4', '0', '8', '9', '0', '6', '2', '8', '5', '8', '3', '4', '8', '9', '7', '7', '1', '8', '5', '9', '7', '0', '6', '1', '9', '4', '0', '5', '9', '9', '6', '1', '0', '0', '4', '6', '0', '3', '6', '9', '2', '9', '1', '9', '9', '"', ',']

theorem object_fragment0437352_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0437352Field007Chars00 ++ tail)) fragment0437352Acc00700 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0437352Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_007"
  err.flush

noncomputable def fragment0437352Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0437352Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '4', '1', '4', '0', '4', '2', '8', '5', '0', '7', '9', '5', '8'])
noncomputable def fragment0437352Acc00900 : List (String × SourceJson) := (fragment0437352Field008Key00, fragment0437352Field008Value00) :: fragment0437352Acc00800
noncomputable def fragment0437352Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '4', '1', '4', '0', '4', '2', '8', '5', '0', '7', '9', '5', '8', '"', ',']

theorem object_fragment0437352_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0437352Field008Chars00 ++ tail)) fragment0437352Acc00800 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0437352Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_008"
  err.flush

noncomputable def fragment0437352Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0437352Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '0', '9', '5', '1', '8', '3', '0', '9', '6', '9', '6', '9', '4'])
noncomputable def fragment0437352Acc01000 : List (String × SourceJson) := (fragment0437352Field009Key00, fragment0437352Field009Value00) :: fragment0437352Acc00900
noncomputable def fragment0437352Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '0', '9', '5', '1', '8', '3', '0', '9', '6', '9', '6', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0437352_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0437352Field009Chars00 ++ tail)) fragment0437352Acc00900 =
      .ok (.obj (fragment0437352Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0437352_object_field_009"
  err.flush

noncomputable def fragment0437352Chars : List Char := '{' :: (fragment0437352Field000Chars00 ++ fragment0437352Field001Chars00 ++ fragment0437352Field002Chars00 ++ fragment0437352Field003Chars00 ++ fragment0437352Field004Chars00 ++ fragment0437352Field005Chars00 ++ fragment0437352Field006Chars00 ++ fragment0437352Field007Chars00 ++ fragment0437352Field008Chars00 ++ fragment0437352Field009Chars00)
noncomputable def fragment0437352Value : SourceJson := .obj (fragment0437352Acc01000.reverse)

theorem value_fragment0437352 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 218) (fragment0437352Chars ++ tail) =
      .ok (fragment0437352Value, tail) := by
  have hinput : fragment0437352Chars ++ tail = '{' :: (fragment0437352Field000Chars00 ++ (fragment0437352Field001Chars00 ++ (fragment0437352Field002Chars00 ++ (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0437352Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 218) (fragment0437352Chars ++ tail) =
        SourceJson.value (fuel + 218) ('{' :: (fragment0437352Field000Chars00 ++ (fragment0437352Field001Chars00 ++ (fragment0437352Field002Chars00 ++ (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 218)) hinput
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0437352Field000Chars00 ++ (fragment0437352Field001Chars00 ++ (fragment0437352Field002Chars00 ++ (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))))))))) fragment0437352Acc00000 := by rfl
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0437352Field001Chars00 ++ (fragment0437352Field002Chars00 ++ (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))))))))) fragment0437352Acc00100 := object_fragment0437352_field_000 fuel (fragment0437352Field001Chars00 ++ (fragment0437352Field002Chars00 ++ (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0437352Field002Chars00 ++ (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))))))) fragment0437352Acc00200 := object_fragment0437352_field_001 fuel (fragment0437352Field002Chars00 ++ (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))))))) fragment0437352Acc00300 := object_fragment0437352_field_002 fuel (fragment0437352Field003Chars00 ++ (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))))) fragment0437352Acc00400 := object_fragment0437352_field_003 fuel (fragment0437352Field004Chars00 ++ (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))))) fragment0437352Acc00500 := object_fragment0437352_field_004 fuel (fragment0437352Field005Chars00 ++ (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))) fragment0437352Acc00600 := object_fragment0437352_field_005 fuel (fragment0437352Field006Chars00 ++ (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))) fragment0437352Acc00700 := object_fragment0437352_field_006 fuel (fragment0437352Field007Chars00 ++ (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))) fragment0437352Acc00800 := object_fragment0437352_field_007 fuel (fragment0437352Field008Chars00 ++ (fragment0437352Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0437352Field009Chars00 ++ (tail))) fragment0437352Acc00900 := object_fragment0437352_field_008 fuel (fragment0437352Field009Chars00 ++ (tail))
    _ = .ok (fragment0437352Value, tail) := object_fragment0437352_field_009 fuel (tail)

noncomputable def fragment0438895Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0438895Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0438895Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '5'])
noncomputable def fragment0438895Acc00100 : List (String × SourceJson) := (fragment0438895Field000Key00, fragment0438895Field000Value00) :: fragment0438895Acc00000
noncomputable def fragment0438895Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '5', ',']

theorem object_fragment0438895_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0438895Field000Chars00 ++ tail)) fragment0438895Acc00000 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0438895Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_000"
  err.flush

noncomputable def fragment0438895Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0438895Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0438895Acc00200 : List (String × SourceJson) := (fragment0438895Field001Key00, fragment0438895Field001Value00) :: fragment0438895Acc00100
noncomputable def fragment0438895Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0438895_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0438895Field001Chars00 ++ tail)) fragment0438895Acc00100 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0438895Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_001"
  err.flush

noncomputable def fragment0438895Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0438895Field002Value00 : SourceJson := .str (String.ofList ['1', '8', '3', '5', '7', '6', '3', '2', '0', '4', '1', '2', '5', '5', '2', '1', '6', '2', '5', '1', '3', '2', '7', '7', '0', '3', '0', '5', '7', '7', '0', '7', '3', '3', '6', '7', '7', '/', '2', '4', '4', '3', '3', '3', '1', '1', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0438895Acc00300 : List (String × SourceJson) := (fragment0438895Field002Key00, fragment0438895Field002Value00) :: fragment0438895Acc00200
noncomputable def fragment0438895Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '8', '3', '5', '7', '6', '3', '2', '0', '4', '1', '2', '5', '5', '2', '1', '6', '2', '5', '1', '3', '2', '7', '7', '0', '3', '0', '5', '7', '7', '0', '7', '3', '3', '6', '7', '7', '/', '2', '4', '4', '3', '3', '3', '1', '1', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0438895_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0438895Field002Chars00 ++ tail)) fragment0438895Acc00200 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0438895Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_002"
  err.flush

noncomputable def fragment0438895Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0438895Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0438895Acc00400 : List (String × SourceJson) := (fragment0438895Field003Key00, fragment0438895Field003Value00) :: fragment0438895Acc00300
noncomputable def fragment0438895Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0438895_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0438895Field003Chars00 ++ tail)) fragment0438895Acc00300 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0438895Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_003"
  err.flush

noncomputable def fragment0438895Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0438895Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0438895Acc00500 : List (String × SourceJson) := (fragment0438895Field004Key00, fragment0438895Field004Value00) :: fragment0438895Acc00400
noncomputable def fragment0438895Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0438895_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0438895Field004Chars00 ++ tail)) fragment0438895Acc00400 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0438895Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_004"
  err.flush

noncomputable def fragment0438895Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0438895Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '8', '1', '2', '8', '5', '4', '6', '2', '9', '/', '1', '0', '4', '9', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '3', '7', '9', '3', '5', '3', '6', '3', '/', '2', '0', '9', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '3', '7', '3', '8', '0', '8', '6', '1', '/', '6', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '4', '8', '9', '4', '1', '1', '2', '6', '3', '/', '4', '1', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '8', '2', '7', '8', '0', '7', '7', '1', '/', '1', '4', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '8', '2', '9', '4', '4', '9', '7', '7', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '7', '9', '6', '0', '4', '0', '2', '1', '/', '3', '3', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '9', '5', '2', '3', '1', '3', '8', '8', '3', '/', '1', '2', '5', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '2', '2', '0', '0', '1', '9', '2', '8', '1', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '0', '6', '6', '1', '7', '1', '0', '7', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0438895Acc00600 : List (String × SourceJson) := (fragment0438895Field005Key00, fragment0438895Field005Value00) :: fragment0438895Acc00500
noncomputable def fragment0438895Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '2', '8', '5', '4', '6', '2', '9', '/', '1', '0', '4', '9', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '3', '7', '9', '3', '5', '3', '6', '3', '/', '2', '0', '9', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '3', '7', '3', '8', '0', '8', '6', '1', '/', '6', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '4', '8', '9', '4', '1', '1', '2', '6', '3', '/', '4', '1', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '8', '2', '7', '8', '0', '7', '7', '1', '/', '1', '4', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '8', '2', '9', '4', '4', '9', '7', '7', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '9', '6', '0', '4', '0', '2', '1', '/', '3', '3', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '9', '5', '2', '3', '1', '3', '8', '8', '3', '/', '1', '2', '5', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '2', '2', '0', '0', '1', '9', '2', '8', '1', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '0', '6', '6', '1', '7', '1', '0', '7', '/', '8', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0438895_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0438895Field005Chars00 ++ tail)) fragment0438895Acc00500 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0438895Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_005"
  err.flush

noncomputable def fragment0438895Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0438895Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '1', '1', '3', '0', '9', '0', '3', '4', '7', '3', '1', '8', '8', '8', '1', '1', '0', '0', '7', '4', '3', '4', '3', '8', '9', '5', '9', '9', '9', '3', '7', '7', '2', '4', '6', '4', '2', '8', '0', '7', '2', '8', '0', '0', '0', '/', '6', '4', '6', '4', '4', '4', '4', '8', '8', '4', '7', '8', '5', '4', '4', '6', '2', '4', '3', '9', '4', '6', '7', '8', '9', '3', '0', '3', '7', '0', '2', '3', '3', '7', '8', '2', '3', '1', '5', '4', '6', '1', '2', '1', '4', '7', '4', '0', '4', '2', '4', '2', '9', '8', '8', '4', '6', '0', '0', '5', '9', '9'])
noncomputable def fragment0438895Acc00700 : List (String × SourceJson) := (fragment0438895Field006Key00, fragment0438895Field006Value00) :: fragment0438895Acc00600
noncomputable def fragment0438895Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '1', '1', '3', '0', '9', '0', '3', '4', '7', '3', '1', '8', '8', '8', '1', '1', '0', '0', '7', '4', '3', '4', '3', '8', '9', '5', '9', '9', '9', '3', '7', '7', '2', '4', '6', '4', '2', '8', '0', '7', '2', '8', '0', '0', '0', '/', '6', '4', '6', '4', '4', '4', '4', '8', '8', '4', '7', '8', '5', '4', '4', '6', '2', '4', '3', '9', '4', '6', '7', '8', '9', '3', '0', '3', '7', '0', '2', '3', '3', '7', '8', '2', '3', '1', '5', '4', '6', '1', '2', '1', '4', '7', '4', '0', '4', '2', '4', '2', '9', '8', '8', '4', '6', '0', '0', '5', '9', '9', '"', ',']

theorem object_fragment0438895_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0438895Field006Chars00 ++ tail)) fragment0438895Acc00600 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0438895Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_006"
  err.flush

noncomputable def fragment0438895Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0438895Field007Value00 : SourceJson := .str (String.ofList ['2', '9', '1', '1', '2', '6', '0', '1', '1', '7', '8', '9', '4', '7', '8', '1', '7', '0', '4', '1', '6', '7', '8', '0', '4', '5', '7', '2', '2', '5', '6', '3', '7', '3', '6', '1', '9', '3', '4', '1', '7', '4', '7', '1', '8', '2', '4', '3', '0', '4', '9', '9', '8', '2', '4', '0', '3', '8', '0', '9', '9', '9', '5', '4', '6', '6', '0', '6', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '2', '1', '6', '2', '4', '8', '6', '3', '5', '7', '8', '9', '8', '5', '8', '6', '0', '8', '9', '8', '1', '7', '4', '1', '9', '8', '2', '8', '4', '7', '6', '1', '4', '7', '8', '7', '6', '1', '7', '8', '6', '3', '6', '5', '5', '6', '4', '4', '0', '9', '0', '7', '4', '4', '7', '2', '6', '5', '6', '5', '4', '9', '0', '7', '4', '6', '7', '2', '3', '3', '0', '5', '6', '1', '9', '2', '0', '0', '7', '4', '8', '3', '9', '3', '3', '1', '5', '0', '9', '6', '7', '6', '1', '6', '5', '5', '7', '2', '6', '1'])
noncomputable def fragment0438895Acc00800 : List (String × SourceJson) := (fragment0438895Field007Key00, fragment0438895Field007Value00) :: fragment0438895Acc00700
noncomputable def fragment0438895Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '9', '1', '1', '2', '6', '0', '1', '1', '7', '8', '9', '4', '7', '8', '1', '7', '0', '4', '1', '6', '7', '8', '0', '4', '5', '7', '2', '2', '5', '6', '3', '7', '3', '6', '1', '9', '3', '4', '1', '7', '4', '7', '1', '8', '2', '4', '3', '0', '4', '9', '9', '8', '2', '4', '0', '3', '8', '0', '9', '9', '9', '5', '4', '6', '6', '0', '6', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '2', '1', '6', '2', '4', '8', '6', '3', '5', '7', '8', '9', '8', '5', '8', '6', '0', '8', '9', '8', '1', '7', '4', '1', '9', '8', '2', '8', '4', '7', '6', '1', '4', '7', '8', '7', '6', '1', '7', '8', '6', '3', '6', '5', '5', '6', '4', '4', '0', '9', '0', '7', '4', '4', '7', '2', '6', '5', '6', '5', '4', '9', '0', '7', '4', '6', '7', '2', '3', '3', '0', '5', '6', '1', '9', '2', '0', '0', '7', '4', '8', '3', '9', '3', '3', '1', '5', '0', '9', '6', '7', '6', '1', '6', '5', '5', '7', '2', '6', '1', '"', ',']

theorem object_fragment0438895_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0438895Field007Chars00 ++ tail)) fragment0438895Acc00700 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0438895Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_007"
  err.flush

noncomputable def fragment0438895Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0438895Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '4', '2', '4', '9', '8', '1', '6', '5', '2', '3', '4', '8'])
noncomputable def fragment0438895Acc00900 : List (String × SourceJson) := (fragment0438895Field008Key00, fragment0438895Field008Value00) :: fragment0438895Acc00800
noncomputable def fragment0438895Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '4', '2', '4', '9', '8', '1', '6', '5', '2', '3', '4', '8', '"', ',']

theorem object_fragment0438895_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0438895Field008Chars00 ++ tail)) fragment0438895Acc00800 =
      SourceJson.object (fuel + 191) (SourceJson.white tail) fragment0438895Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_008"
  err.flush

noncomputable def fragment0438895Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0438895Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '7', '7', '1', '5', '1', '1', '6', '0', '3', '4', '1', '8'])
noncomputable def fragment0438895Acc01000 : List (String × SourceJson) := (fragment0438895Field009Key00, fragment0438895Field009Value00) :: fragment0438895Acc00900
noncomputable def fragment0438895Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '5', '7', '7', '1', '5', '1', '1', '6', '0', '3', '4', '1', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0438895_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0438895Field009Chars00 ++ tail)) fragment0438895Acc00900 =
      .ok (.obj (fragment0438895Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0438895_object_field_009"
  err.flush

noncomputable def fragment0438895Chars : List Char := '{' :: (fragment0438895Field000Chars00 ++ fragment0438895Field001Chars00 ++ fragment0438895Field002Chars00 ++ fragment0438895Field003Chars00 ++ fragment0438895Field004Chars00 ++ fragment0438895Field005Chars00 ++ fragment0438895Field006Chars00 ++ fragment0438895Field007Chars00 ++ fragment0438895Field008Chars00 ++ fragment0438895Field009Chars00)
noncomputable def fragment0438895Value : SourceJson := .obj (fragment0438895Acc01000.reverse)

theorem value_fragment0438895 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 201) (fragment0438895Chars ++ tail) =
      .ok (fragment0438895Value, tail) := by
  have hinput : fragment0438895Chars ++ tail = '{' :: (fragment0438895Field000Chars00 ++ (fragment0438895Field001Chars00 ++ (fragment0438895Field002Chars00 ++ (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0438895Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 201) (fragment0438895Chars ++ tail) =
        SourceJson.value (fuel + 201) ('{' :: (fragment0438895Field000Chars00 ++ (fragment0438895Field001Chars00 ++ (fragment0438895Field002Chars00 ++ (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 201)) hinput
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0438895Field000Chars00 ++ (fragment0438895Field001Chars00 ++ (fragment0438895Field002Chars00 ++ (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))))))))) fragment0438895Acc00000 := by rfl
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0438895Field001Chars00 ++ (fragment0438895Field002Chars00 ++ (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))))))))) fragment0438895Acc00100 := object_fragment0438895_field_000 fuel (fragment0438895Field001Chars00 ++ (fragment0438895Field002Chars00 ++ (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0438895Field002Chars00 ++ (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))))))) fragment0438895Acc00200 := object_fragment0438895_field_001 fuel (fragment0438895Field002Chars00 ++ (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))))))) fragment0438895Acc00300 := object_fragment0438895_field_002 fuel (fragment0438895Field003Chars00 ++ (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))))) fragment0438895Acc00400 := object_fragment0438895_field_003 fuel (fragment0438895Field004Chars00 ++ (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))))) fragment0438895Acc00500 := object_fragment0438895_field_004 fuel (fragment0438895Field005Chars00 ++ (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))) fragment0438895Acc00600 := object_fragment0438895_field_005 fuel (fragment0438895Field006Chars00 ++ (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))) fragment0438895Acc00700 := object_fragment0438895_field_006 fuel (fragment0438895Field007Chars00 ++ (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))) fragment0438895Acc00800 := object_fragment0438895_field_007 fuel (fragment0438895Field008Chars00 ++ (fragment0438895Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0438895Field009Chars00 ++ (tail))) fragment0438895Acc00900 := object_fragment0438895_field_008 fuel (fragment0438895Field009Chars00 ++ (tail))
    _ = .ok (fragment0438895Value, tail) := object_fragment0438895_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0124_before_reader"
  err.flush

noncomputable def chunk0124LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0124SuffixChars00 : List Char := [',']
noncomputable def chunk0124Chars00 : List Char := chunk0124LeadChars00 ++ fragment0437352Chars ++ chunk0124SuffixChars00
noncomputable def chunk0124Push00 (acc : List SourceJson) : List SourceJson := fragment0437352Value :: acc

noncomputable def chunk0124AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0124_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 480)
      (SourceJson.white (chunk0124LeadChars00 ++ (fragment0437352Chars ++ rest))) acc =
      (SourceJson.value (fuel + 479) (fragment0437352Chars ++ rest)).bind
        (chunk0124AfterValue00 (fuel + 479) acc) := by rfl

theorem array_chunk0124 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 480) (SourceJson.white (chunk0124Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 479) (SourceJson.white tail) (chunk0124Push00 acc) := by
  have hinput : chunk0124Chars00 ++ tail = chunk0124LeadChars00 ++ (fragment0437352Chars ++ (chunk0124SuffixChars00 ++ tail)) := by
    simp only [chunk0124Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 480) (SourceJson.white (chunk0124Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 480)
          (SourceJson.white (chunk0124LeadChars00 ++ (fragment0437352Chars ++ (chunk0124SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 480) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 479) (fragment0437352Chars ++ (chunk0124SuffixChars00 ++ tail))).bind
        (chunk0124AfterValue00 (fuel + 479) acc) := array_chunk0124_head fuel (chunk0124SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0437352Value, chunk0124SuffixChars00 ++ tail)).bind
        (chunk0124AfterValue00 (fuel + 479) acc) :=
      congrArg (fun result => result.bind (chunk0124AfterValue00 (fuel + 479) acc))
        (value_fragment0437352 (fuel + 261) (chunk0124SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 479) (SourceJson.white tail) (chunk0124Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0124_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0125_before_reader"
  err.flush

noncomputable def chunk0125LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0125SuffixChars00 : List Char := [',']
noncomputable def chunk0125Chars00 : List Char := chunk0125LeadChars00 ++ fragment0438895Chars ++ chunk0125SuffixChars00
noncomputable def chunk0125Push00 (acc : List SourceJson) : List SourceJson := fragment0438895Value :: acc

noncomputable def chunk0125AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0125_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 479)
      (SourceJson.white (chunk0125LeadChars00 ++ (fragment0438895Chars ++ rest))) acc =
      (SourceJson.value (fuel + 478) (fragment0438895Chars ++ rest)).bind
        (chunk0125AfterValue00 (fuel + 478) acc) := by rfl

theorem array_chunk0125 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 479) (SourceJson.white (chunk0125Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 478) (SourceJson.white tail) (chunk0125Push00 acc) := by
  have hinput : chunk0125Chars00 ++ tail = chunk0125LeadChars00 ++ (fragment0438895Chars ++ (chunk0125SuffixChars00 ++ tail)) := by
    simp only [chunk0125Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 479) (SourceJson.white (chunk0125Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 479)
          (SourceJson.white (chunk0125LeadChars00 ++ (fragment0438895Chars ++ (chunk0125SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 479) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 478) (fragment0438895Chars ++ (chunk0125SuffixChars00 ++ tail))).bind
        (chunk0125AfterValue00 (fuel + 478) acc) := array_chunk0125_head fuel (chunk0125SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0438895Value, chunk0125SuffixChars00 ++ tail)).bind
        (chunk0125AfterValue00 (fuel + 478) acc) :=
      congrArg (fun result => result.bind (chunk0125AfterValue00 (fuel + 478) acc))
        (value_fragment0438895 (fuel + 277) (chunk0125SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 478) (SourceJson.white tail) (chunk0125Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0125_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0124Chars00 ++ chunk0125Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0125Push00 (chunk0124Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 480) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 478) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0124Chars00 ++ (chunk0125Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 480) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 480) (SourceJson.white (chunk0124Chars00 ++ (chunk0125Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 480) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 479) (SourceJson.white (chunk0125Chars00 ++ (tail))) (chunk0124Push00 (acc)) := array_chunk0124 fuel (chunk0125Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 478) (SourceJson.white tail) (blockPush acc) := array_chunk0125 fuel (tail) (chunk0124Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 437346).take 3064 = blockChars := by rfl

theorem block_original_split : sourceRest 437346 = blockChars ++ sourceRest 440410 := by
  calc
    sourceRest 437346 = (sourceRest 437346).take 3064 ++ (sourceRest 437346).drop 3064 :=
      (List.take_append_drop 3064 (sourceRest 437346)).symm
    _ = blockChars ++ (sourceRest 437346).drop 3064 :=
      congrArg (fun part => part ++ (sourceRest 437346).drop 3064) block_original_prefix
    _ = blockChars ++ sourceRest 440410 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 437346 3064)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 480) (SourceJson.white (sourceRest 437346)) acc =
      SourceJson.array (fuel + 478) (SourceJson.white (sourceRest 440410)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 480) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 440410) acc)

#print axioms object_fragment0437352_field_000
#print axioms object_fragment0437352_field_001
#print axioms object_fragment0437352_field_002
#print axioms object_fragment0437352_field_003
#print axioms object_fragment0437352_field_004
#print axioms object_fragment0437352_field_005
#print axioms object_fragment0437352_field_006
#print axioms object_fragment0437352_field_007
#print axioms object_fragment0437352_field_008
#print axioms object_fragment0437352_field_009
#print axioms value_fragment0437352
#print axioms object_fragment0438895_field_000
#print axioms object_fragment0438895_field_001
#print axioms object_fragment0438895_field_002
#print axioms object_fragment0438895_field_003
#print axioms object_fragment0438895_field_004
#print axioms object_fragment0438895_field_005
#print axioms object_fragment0438895_field_006
#print axioms object_fragment0438895_field_007
#print axioms object_fragment0438895_field_008
#print axioms object_fragment0438895_field_009
#print axioms value_fragment0438895
#print axioms array_chunk0124_head
#print axioms array_chunk0124
#print axioms array_chunk0125_head
#print axioms array_chunk0125
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock063

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
