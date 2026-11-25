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

namespace SimplicesBlock040

noncomputable def fragment0360409Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0360409Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0360409Field000Value00 : SourceJson := .number (String.ofList ['7', '9'])
noncomputable def fragment0360409Acc00100 : List (String × SourceJson) := (fragment0360409Field000Key00, fragment0360409Field000Value00) :: fragment0360409Acc00000
noncomputable def fragment0360409Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', '9', ',']

theorem object_fragment0360409_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0360409Field000Chars00 ++ tail)) fragment0360409Acc00000 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0360409Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_000"
  err.flush

noncomputable def fragment0360409Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0360409Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0360409Acc00200 : List (String × SourceJson) := (fragment0360409Field001Key00, fragment0360409Field001Value00) :: fragment0360409Acc00100
noncomputable def fragment0360409Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0360409_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0360409Field001Chars00 ++ tail)) fragment0360409Acc00100 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0360409Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_001"
  err.flush

noncomputable def fragment0360409Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0360409Field002Value00 : SourceJson := .str (String.ofList ['3', '4', '3', '4', '7', '9', '9', '3', '8', '3', '6', '9', '6', '9', '0', '2', '0', '0', '5', '8', '8', '3', '5', '9', '9', '3', '2', '3', '8', '5', '5', '6', '1', '5', '2', '3', '7', '/', '7', '0', '9', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0360409Acc00300 : List (String × SourceJson) := (fragment0360409Field002Key00, fragment0360409Field002Value00) :: fragment0360409Acc00200
noncomputable def fragment0360409Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '4', '3', '4', '7', '9', '9', '3', '8', '3', '6', '9', '6', '9', '0', '2', '0', '0', '5', '8', '8', '3', '5', '9', '9', '3', '2', '3', '8', '5', '5', '6', '1', '5', '2', '3', '7', '/', '7', '0', '9', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0360409_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0360409Field002Chars00 ++ tail)) fragment0360409Acc00200 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0360409Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_002"
  err.flush

noncomputable def fragment0360409Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0360409Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0360409Acc00400 : List (String × SourceJson) := (fragment0360409Field003Key00, fragment0360409Field003Value00) :: fragment0360409Acc00300
noncomputable def fragment0360409Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0360409_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0360409Field003Chars00 ++ tail)) fragment0360409Acc00300 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0360409Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_003"
  err.flush

noncomputable def fragment0360409Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0360409Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0360409Acc00500 : List (String × SourceJson) := (fragment0360409Field004Key00, fragment0360409Field004Value00) :: fragment0360409Acc00400
noncomputable def fragment0360409Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0360409_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0360409Field004Chars00 ++ tail)) fragment0360409Acc00400 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0360409Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_004"
  err.flush

noncomputable def fragment0360409Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0360409Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '1', '5', '5', '7', '4', '2', '2', '7', '8', '7', '/', '3', '4', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '3', '4', '4', '8', '6', '9', '2', '5', '2', '9', '/', '2', '4', '2', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '0', '0', '5', '2', '4', '3', '7', '2', '1', '/', '1', '3', '9', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '2', '9', '7', '0', '8', '5', '7', '0', '2', '9', '/', '1', '3', '6', '1', '5', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '8', '0', '0', '2', '6', '5', '4', '4', '6', '7', '/', '7', '2', '6', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '1', '5', '1', '2', '5', '0', '7', '3', '9', '/', '1', '8', '1', '5', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '6', '7', '2', '7', '2', '5', '4', '1', '1', '/', '5', '4', '4', '6', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '3', '5', '9', '0', '6', '8', '2', '9', '/', '4', '3', '5', '7', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '9', '2', '5', '3', '7', '1', '4', '1', '/', '1', '0', '8', '9', '2', '7', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '7', '9', '2', '2', '6', '8', '2', '9', '3', '/', '5', '4', '4', '6', '3', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0360409Acc00600 : List (String × SourceJson) := (fragment0360409Field005Key00, fragment0360409Field005Value00) :: fragment0360409Acc00500
noncomputable def fragment0360409Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '5', '7', '4', '2', '2', '7', '8', '7', '/', '3', '4', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '4', '4', '8', '6', '9', '2', '5', '2', '9', '/', '2', '4', '2', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '0', '5', '2', '4', '3', '7', '2', '1', '/', '1', '3', '9', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '9', '7', '0', '8', '5', '7', '0', '2', '9', '/', '1', '3', '6', '1', '5', '8', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '8', '0', '0', '2', '6', '5', '4', '4', '6', '7', '/', '7', '2', '6', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '5', '1', '2', '5', '0', '7', '3', '9', '/', '1', '8', '1', '5', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '7', '2', '7', '2', '5', '4', '1', '1', '/', '5', '4', '4', '6', '3', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '3', '5', '9', '0', '6', '8', '2', '9', '/', '4', '3', '5', '7', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '9', '2', '5', '3', '7', '1', '4', '1', '/', '1', '0', '8', '9', '2', '7', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '7', '9', '2', '2', '6', '8', '2', '9', '3', '/', '5', '4', '4', '6', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0360409_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0360409Field005Chars00 ++ tail)) fragment0360409Acc00500 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0360409Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_005"
  err.flush

noncomputable def fragment0360409Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0360409Field006Value00 : SourceJson := .str (String.ofList ['5', '2', '3', '6', '6', '6', '7', '4', '1', '2', '2', '6', '5', '5', '7', '2', '8', '3', '0', '6', '5', '4', '5', '2', '5', '0', '2', '4', '5', '9', '4', '4', '7', '4', '9', '0', '3', '8', '0', '9', '6', '5', '3', '8', '0', '9', '1', '5', '2', '0', '0', '0', '0', '/', '2', '2', '2', '7', '1', '1', '5', '0', '4', '8', '3', '6', '5', '3', '1', '1', '1', '9', '3', '7', '5', '6', '5', '3', '5', '3', '3', '3', '4', '2', '5', '9', '0', '1', '2', '8', '6', '6', '3', '0', '0', '8', '1', '4', '9', '3', '6', '9', '0', '5', '0', '5', '2', '2', '4', '4', '8', '7', '4', '7', '4', '5', '4', '7'])
noncomputable def fragment0360409Acc00700 : List (String × SourceJson) := (fragment0360409Field006Key00, fragment0360409Field006Value00) :: fragment0360409Acc00600
noncomputable def fragment0360409Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '2', '3', '6', '6', '6', '7', '4', '1', '2', '2', '6', '5', '5', '7', '2', '8', '3', '0', '6', '5', '4', '5', '2', '5', '0', '2', '4', '5', '9', '4', '4', '7', '4', '9', '0', '3', '8', '0', '9', '6', '5', '3', '8', '0', '9', '1', '5', '2', '0', '0', '0', '0', '/', '2', '2', '2', '7', '1', '1', '5', '0', '4', '8', '3', '6', '5', '3', '1', '1', '1', '9', '3', '7', '5', '6', '5', '3', '5', '3', '3', '3', '4', '2', '5', '9', '0', '1', '2', '8', '6', '6', '3', '0', '0', '8', '1', '4', '9', '3', '6', '9', '0', '5', '0', '5', '2', '2', '4', '4', '8', '7', '4', '7', '4', '5', '4', '7', '"', ',']

theorem object_fragment0360409_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0360409Field006Chars00 ++ tail)) fragment0360409Acc00600 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0360409Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_006"
  err.flush

noncomputable def fragment0360409Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0360409Field007Value00 : SourceJson := .str (String.ofList ['3', '8', '4', '4', '8', '9', '2', '2', '2', '3', '2', '7', '4', '7', '5', '9', '0', '5', '6', '6', '0', '1', '3', '9', '0', '6', '2', '7', '8', '7', '8', '9', '2', '4', '3', '1', '4', '5', '7', '4', '7', '0', '3', '7', '1', '7', '6', '5', '7', '4', '2', '4', '2', '0', '8', '0', '5', '0', '0', '6', '0', '1', '4', '2', '9', '5', '9', '7', '4', '2', '5', '8', '3', '1', '2', '0', '5', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '0', '6', '6', '2', '9', '7', '8', '5', '4', '7', '9', '4', '7', '3', '0', '4', '4', '2', '0', '3', '4', '9', '2', '9', '5', '5', '8', '2', '8', '7', '4', '7', '7', '8', '7', '7', '0', '6', '4', '7', '6', '1', '8', '8', '2', '0', '5', '1', '6', '4', '8', '9', '0', '9', '1', '3', '1', '2', '1', '4', '9', '8', '5', '4', '7', '5', '0', '5', '7', '1', '1', '3', '1', '5', '1', '4', '0', '9', '2', '8', '1', '7', '0', '1', '3', '9', '7', '5', '1', '6', '8', '8', '9', '1', '3', '7', '3', '3', '9', '9', '7', '6', '8', '7', '1'])
noncomputable def fragment0360409Acc00800 : List (String × SourceJson) := (fragment0360409Field007Key00, fragment0360409Field007Value00) :: fragment0360409Acc00700
noncomputable def fragment0360409Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '8', '4', '4', '8', '9', '2', '2', '2', '3', '2', '7', '4', '7', '5', '9', '0', '5', '6', '6', '0', '1', '3', '9', '0', '6', '2', '7', '8', '7', '8', '9', '2', '4', '3', '1', '4', '5', '7', '4', '7', '0', '3', '7', '1', '7', '6', '5', '7', '4', '2', '4', '2', '0', '8', '0', '5', '0', '0', '6', '0', '1', '4', '2', '9', '5', '9', '7', '4', '2', '5', '8', '3', '1', '2', '0', '5', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '0', '6', '6', '2', '9', '7', '8', '5', '4', '7', '9', '4', '7', '3', '0', '4', '4', '2', '0', '3', '4', '9', '2', '9', '5', '5', '8', '2', '8', '7', '4', '7', '7', '8', '7', '7', '0', '6', '4', '7', '6', '1', '8', '8', '2', '0', '5', '1', '6', '4', '8', '9', '0', '9', '1', '3', '1', '2', '1', '4', '9', '8', '5', '4', '7', '5', '0', '5', '7', '1', '1', '3', '1', '5', '1', '4', '0', '9', '2', '8', '1', '7', '0', '1', '3', '9', '7', '5', '1', '6', '8', '8', '9', '1', '3', '7', '3', '3', '9', '9', '7', '6', '8', '7', '1', '"', ',']

theorem object_fragment0360409_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0360409Field007Chars00 ++ tail)) fragment0360409Acc00700 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0360409Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_007"
  err.flush

noncomputable def fragment0360409Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0360409Field008Value00 : SourceJson := .str (String.ofList ['1', '8', '6', '2', '9', '1', '0', '2', '1', '2', '3', '6', '9', '3', '9', '1', '2', '2', '8'])
noncomputable def fragment0360409Acc00900 : List (String × SourceJson) := (fragment0360409Field008Key00, fragment0360409Field008Value00) :: fragment0360409Acc00800
noncomputable def fragment0360409Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '6', '2', '9', '1', '0', '2', '1', '2', '3', '6', '9', '3', '9', '1', '2', '2', '8', '"', ',']

theorem object_fragment0360409_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0360409Field008Chars00 ++ tail)) fragment0360409Acc00800 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0360409Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_008"
  err.flush

noncomputable def fragment0360409Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0360409Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '4', '6', '0', '2', '4', '1', '0', '9', '2', '9', '1', '2', '8', '0', '9', '7', '9', '4'])
noncomputable def fragment0360409Acc01000 : List (String × SourceJson) := (fragment0360409Field009Key00, fragment0360409Field009Value00) :: fragment0360409Acc00900
noncomputable def fragment0360409Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '4', '6', '0', '2', '4', '1', '0', '9', '2', '9', '1', '2', '8', '0', '9', '7', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0360409_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0360409Field009Chars00 ++ tail)) fragment0360409Acc00900 =
      .ok (.obj (fragment0360409Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0360409_object_field_009"
  err.flush

noncomputable def fragment0360409Chars : List Char := '{' :: (fragment0360409Field000Chars00 ++ fragment0360409Field001Chars00 ++ fragment0360409Field002Chars00 ++ fragment0360409Field003Chars00 ++ fragment0360409Field004Chars00 ++ fragment0360409Field005Chars00 ++ fragment0360409Field006Chars00 ++ fragment0360409Field007Chars00 ++ fragment0360409Field008Chars00 ++ fragment0360409Field009Chars00)
noncomputable def fragment0360409Value : SourceJson := .obj (fragment0360409Acc01000.reverse)

theorem value_fragment0360409 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 216) (fragment0360409Chars ++ tail) =
      .ok (fragment0360409Value, tail) := by
  have hinput : fragment0360409Chars ++ tail = '{' :: (fragment0360409Field000Chars00 ++ (fragment0360409Field001Chars00 ++ (fragment0360409Field002Chars00 ++ (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0360409Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 216) (fragment0360409Chars ++ tail) =
        SourceJson.value (fuel + 216) ('{' :: (fragment0360409Field000Chars00 ++ (fragment0360409Field001Chars00 ++ (fragment0360409Field002Chars00 ++ (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 216)) hinput
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0360409Field000Chars00 ++ (fragment0360409Field001Chars00 ++ (fragment0360409Field002Chars00 ++ (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))))))))) fragment0360409Acc00000 := by rfl
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0360409Field001Chars00 ++ (fragment0360409Field002Chars00 ++ (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))))))))) fragment0360409Acc00100 := object_fragment0360409_field_000 fuel (fragment0360409Field001Chars00 ++ (fragment0360409Field002Chars00 ++ (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0360409Field002Chars00 ++ (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))))))) fragment0360409Acc00200 := object_fragment0360409_field_001 fuel (fragment0360409Field002Chars00 ++ (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))))))) fragment0360409Acc00300 := object_fragment0360409_field_002 fuel (fragment0360409Field003Chars00 ++ (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))))) fragment0360409Acc00400 := object_fragment0360409_field_003 fuel (fragment0360409Field004Chars00 ++ (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))))) fragment0360409Acc00500 := object_fragment0360409_field_004 fuel (fragment0360409Field005Chars00 ++ (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))) fragment0360409Acc00600 := object_fragment0360409_field_005 fuel (fragment0360409Field006Chars00 ++ (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))) fragment0360409Acc00700 := object_fragment0360409_field_006 fuel (fragment0360409Field007Chars00 ++ (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))) fragment0360409Acc00800 := object_fragment0360409_field_007 fuel (fragment0360409Field008Chars00 ++ (fragment0360409Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0360409Field009Chars00 ++ (tail))) fragment0360409Acc00900 := object_fragment0360409_field_008 fuel (fragment0360409Field009Chars00 ++ (tail))
    _ = .ok (fragment0360409Value, tail) := object_fragment0360409_field_009 fuel (tail)

noncomputable def fragment0361975Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0361975Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0361975Field000Value00 : SourceJson := .number (String.ofList ['8', '0'])
noncomputable def fragment0361975Acc00100 : List (String × SourceJson) := (fragment0361975Field000Key00, fragment0361975Field000Value00) :: fragment0361975Acc00000
noncomputable def fragment0361975Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '0', ',']

theorem object_fragment0361975_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0361975Field000Chars00 ++ tail)) fragment0361975Acc00000 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0361975Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_000"
  err.flush

noncomputable def fragment0361975Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0361975Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0361975Acc00200 : List (String × SourceJson) := (fragment0361975Field001Key00, fragment0361975Field001Value00) :: fragment0361975Acc00100
noncomputable def fragment0361975Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0361975_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0361975Field001Chars00 ++ tail)) fragment0361975Acc00100 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0361975Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_001"
  err.flush

noncomputable def fragment0361975Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0361975Field002Value00 : SourceJson := .str (String.ofList ['9', '4', '5', '1', '8', '9', '0', '0', '0', '7', '5', '1', '9', '3', '1', '4', '9', '0', '1', '8', '1', '3', '8', '9', '8', '4', '0', '2', '4', '7', '8', '7', '5', '0', '5', '5', '7', '6', '1', '7', '0', '9', '/', '1', '2', '0', '0', '9', '3', '8', '8', '7', '6', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0361975Acc00300 : List (String × SourceJson) := (fragment0361975Field002Key00, fragment0361975Field002Value00) :: fragment0361975Acc00200
noncomputable def fragment0361975Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '4', '5', '1', '8', '9', '0', '0', '0', '7', '5', '1', '9', '3', '1', '4', '9', '0', '1', '8', '1', '3', '8', '9', '8', '4', '0', '2', '4', '7', '8', '7', '5', '0', '5', '5', '7', '6', '1', '7', '0', '9', '/', '1', '2', '0', '0', '9', '3', '8', '8', '7', '6', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0361975_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0361975Field002Chars00 ++ tail)) fragment0361975Acc00200 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0361975Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_002"
  err.flush

noncomputable def fragment0361975Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0361975Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0361975Acc00400 : List (String × SourceJson) := (fragment0361975Field003Key00, fragment0361975Field003Value00) :: fragment0361975Acc00300
noncomputable def fragment0361975Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0361975_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0361975Field003Chars00 ++ tail)) fragment0361975Acc00300 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0361975Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_003"
  err.flush

noncomputable def fragment0361975Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0361975Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0361975Acc00500 : List (String × SourceJson) := (fragment0361975Field004Key00, fragment0361975Field004Value00) :: fragment0361975Acc00400
noncomputable def fragment0361975Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0361975_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0361975Field004Chars00 ++ tail)) fragment0361975Acc00400 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0361975Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_004"
  err.flush

noncomputable def fragment0361975Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0361975Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '3', '9', '2', '3', '3', '1', '0', '0', '9', '/', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '4', '2', '2', '1', '9', '6', '0', '3', '/', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '0', '3', '1', '4', '5', '7', '6', '7', '1', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '7', '5', '4', '2', '6', '6', '1', '7', '/', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '7', '8', '5', '2', '6', '9', '9', '5', '7', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '1', '9', '4', '9', '7', '2', '0', '9', '/', '4', '1', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '7', '3', '9', '7', '9', '7', '3', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '7', '2', '2', '3', '0', '8', '9', '1', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '6', '0', '7', '7', '1', '7', '1', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '9', '1', '1', '3', '6', '9', '2', '7', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0361975Acc00600 : List (String × SourceJson) := (fragment0361975Field005Key00, fragment0361975Field005Value00) :: fragment0361975Acc00500
noncomputable def fragment0361975Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '2', '3', '3', '1', '0', '0', '9', '/', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '4', '2', '2', '1', '9', '6', '0', '3', '/', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '0', '3', '1', '4', '5', '7', '6', '7', '1', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '7', '5', '4', '2', '6', '6', '1', '7', '/', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '7', '8', '5', '2', '6', '9', '9', '5', '7', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '1', '9', '4', '9', '7', '2', '0', '9', '/', '4', '1', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '7', '3', '9', '7', '9', '7', '3', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '7', '2', '2', '3', '0', '8', '9', '1', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '6', '0', '7', '7', '1', '7', '1', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '9', '1', '1', '3', '6', '9', '2', '7', '/', '8', '3', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0361975_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0361975Field005Chars00 ++ tail)) fragment0361975Acc00500 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0361975Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_005"
  err.flush

noncomputable def fragment0361975Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0361975Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '2', '5', '8', '0', '2', '7', '5', '0', '2', '4', '6', '3', '8', '0', '9', '5', '6', '1', '0', '1', '7', '1', '7', '5', '2', '9', '0', '4', '3', '2', '9', '7', '9', '5', '4', '4', '0', '0', '2', '7', '1', '4', '0', '1', '2', '7', '2', '4', '2', '8', '8', '0', '0', '0', '0', '/', '2', '9', '4', '6', '4', '7', '3', '2', '0', '8', '9', '8', '7', '3', '0', '6', '7', '0', '9', '3', '3', '9', '8', '9', '6', '2', '4', '6', '1', '2', '2', '4', '6', '7', '4', '0', '2', '2', '1', '1', '5', '9', '7', '8', '1', '6', '1', '5', '2', '5', '3', '8', '4', '1', '1', '9', '9', '6', '9', '2', '8', '8', '2', '5', '6', '8', '1'])
noncomputable def fragment0361975Acc00700 : List (String × SourceJson) := (fragment0361975Field006Key00, fragment0361975Field006Value00) :: fragment0361975Acc00600
noncomputable def fragment0361975Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '2', '5', '8', '0', '2', '7', '5', '0', '2', '4', '6', '3', '8', '0', '9', '5', '6', '1', '0', '1', '7', '1', '7', '5', '2', '9', '0', '4', '3', '2', '9', '7', '9', '5', '4', '4', '0', '0', '2', '7', '1', '4', '0', '1', '2', '7', '2', '4', '2', '8', '8', '0', '0', '0', '0', '/', '2', '9', '4', '6', '4', '7', '3', '2', '0', '8', '9', '8', '7', '3', '0', '6', '7', '0', '9', '3', '3', '9', '8', '9', '6', '2', '4', '6', '1', '2', '2', '4', '6', '7', '4', '0', '2', '2', '1', '1', '5', '9', '7', '8', '1', '6', '1', '5', '2', '5', '3', '8', '4', '1', '1', '9', '9', '6', '9', '2', '8', '8', '2', '5', '6', '8', '1', '"', ',']

theorem object_fragment0361975_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0361975Field006Chars00 ++ tail)) fragment0361975Acc00600 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0361975Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_006"
  err.flush

noncomputable def fragment0361975Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0361975Field007Value00 : SourceJson := .str (String.ofList ['7', '0', '7', '1', '7', '4', '7', '1', '6', '3', '4', '2', '1', '6', '4', '5', '8', '7', '8', '9', '6', '1', '9', '7', '5', '3', '0', '2', '1', '5', '8', '8', '5', '7', '0', '5', '3', '3', '6', '5', '8', '1', '6', '0', '6', '9', '6', '8', '4', '7', '8', '6', '9', '1', '1', '0', '0', '9', '0', '3', '1', '1', '2', '1', '3', '2', '7', '0', '7', '3', '9', '6', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '9', '6', '3', '2', '9', '2', '3', '1', '3', '7', '6', '1', '8', '9', '2', '2', '6', '0', '2', '0', '2', '0', '0', '1', '7', '8', '0', '3', '9', '1', '5', '3', '7', '8', '8', '7', '5', '2', '6', '0', '6', '8', '6', '3', '6', '1', '0', '6', '7', '9', '2', '4', '7', '1', '0', '8', '7', '4', '1', '9', '4', '6', '8', '9', '3', '4', '0', '5', '9', '4', '7', '7', '0', '9', '2', '0', '1', '2', '6', '0', '2', '0', '7', '6', '5', '5', '2', '4', '9', '5', '5', '6', '7', '1', '6', '9', '2', '6', '3'])
noncomputable def fragment0361975Acc00800 : List (String × SourceJson) := (fragment0361975Field007Key00, fragment0361975Field007Value00) :: fragment0361975Acc00700
noncomputable def fragment0361975Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '7', '1', '7', '4', '7', '1', '6', '3', '4', '2', '1', '6', '4', '5', '8', '7', '8', '9', '6', '1', '9', '7', '5', '3', '0', '2', '1', '5', '8', '8', '5', '7', '0', '5', '3', '3', '6', '5', '8', '1', '6', '0', '6', '9', '6', '8', '4', '7', '8', '6', '9', '1', '1', '0', '0', '9', '0', '3', '1', '1', '2', '1', '3', '2', '7', '0', '7', '3', '9', '6', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '9', '6', '3', '2', '9', '2', '3', '1', '3', '7', '6', '1', '8', '9', '2', '2', '6', '0', '2', '0', '2', '0', '0', '1', '7', '8', '0', '3', '9', '1', '5', '3', '7', '8', '8', '7', '5', '2', '6', '0', '6', '8', '6', '3', '6', '1', '0', '6', '7', '9', '2', '4', '7', '1', '0', '8', '7', '4', '1', '9', '4', '6', '8', '9', '3', '4', '0', '5', '9', '4', '7', '7', '0', '9', '2', '0', '1', '2', '6', '0', '2', '0', '7', '6', '5', '5', '2', '4', '9', '5', '5', '6', '7', '1', '6', '9', '2', '6', '3', '"', ',']

theorem object_fragment0361975_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0361975Field007Chars00 ++ tail)) fragment0361975Acc00700 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0361975Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_007"
  err.flush

noncomputable def fragment0361975Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0361975Field008Value00 : SourceJson := .str (String.ofList ['3', '0', '2', '7', '1', '8', '7', '9', '9', '4', '9', '0', '3', '9', '8', '7', '1', '1', '7'])
noncomputable def fragment0361975Acc00900 : List (String × SourceJson) := (fragment0361975Field008Key00, fragment0361975Field008Value00) :: fragment0361975Acc00800
noncomputable def fragment0361975Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '2', '7', '1', '8', '7', '9', '9', '4', '9', '0', '3', '9', '8', '7', '1', '1', '7', '"', ',']

theorem object_fragment0361975_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0361975Field008Chars00 ++ tail)) fragment0361975Acc00800 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0361975Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_008"
  err.flush

noncomputable def fragment0361975Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0361975Field009Value00 : SourceJson := .str (String.ofList ['2', '3', '3', '8', '0', '8', '2', '4', '5', '6', '2', '3', '0', '7', '4', '7', '6', '2', '5', '8'])
noncomputable def fragment0361975Acc01000 : List (String × SourceJson) := (fragment0361975Field009Key00, fragment0361975Field009Value00) :: fragment0361975Acc00900
noncomputable def fragment0361975Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '3', '8', '0', '8', '2', '4', '5', '6', '2', '3', '0', '7', '4', '7', '6', '2', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0361975_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0361975Field009Chars00 ++ tail)) fragment0361975Acc00900 =
      .ok (.obj (fragment0361975Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0361975_object_field_009"
  err.flush

noncomputable def fragment0361975Chars : List Char := '{' :: (fragment0361975Field000Chars00 ++ fragment0361975Field001Chars00 ++ fragment0361975Field002Chars00 ++ fragment0361975Field003Chars00 ++ fragment0361975Field004Chars00 ++ fragment0361975Field005Chars00 ++ fragment0361975Field006Chars00 ++ fragment0361975Field007Chars00 ++ fragment0361975Field008Chars00 ++ fragment0361975Field009Chars00)
noncomputable def fragment0361975Value : SourceJson := .obj (fragment0361975Acc01000.reverse)

theorem value_fragment0361975 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 204) (fragment0361975Chars ++ tail) =
      .ok (fragment0361975Value, tail) := by
  have hinput : fragment0361975Chars ++ tail = '{' :: (fragment0361975Field000Chars00 ++ (fragment0361975Field001Chars00 ++ (fragment0361975Field002Chars00 ++ (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0361975Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 204) (fragment0361975Chars ++ tail) =
        SourceJson.value (fuel + 204) ('{' :: (fragment0361975Field000Chars00 ++ (fragment0361975Field001Chars00 ++ (fragment0361975Field002Chars00 ++ (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 204)) hinput
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0361975Field000Chars00 ++ (fragment0361975Field001Chars00 ++ (fragment0361975Field002Chars00 ++ (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))))))))) fragment0361975Acc00000 := by rfl
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0361975Field001Chars00 ++ (fragment0361975Field002Chars00 ++ (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))))))))) fragment0361975Acc00100 := object_fragment0361975_field_000 fuel (fragment0361975Field001Chars00 ++ (fragment0361975Field002Chars00 ++ (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0361975Field002Chars00 ++ (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))))))) fragment0361975Acc00200 := object_fragment0361975_field_001 fuel (fragment0361975Field002Chars00 ++ (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))))))) fragment0361975Acc00300 := object_fragment0361975_field_002 fuel (fragment0361975Field003Chars00 ++ (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))))) fragment0361975Acc00400 := object_fragment0361975_field_003 fuel (fragment0361975Field004Chars00 ++ (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))))) fragment0361975Acc00500 := object_fragment0361975_field_004 fuel (fragment0361975Field005Chars00 ++ (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))) fragment0361975Acc00600 := object_fragment0361975_field_005 fuel (fragment0361975Field006Chars00 ++ (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))) fragment0361975Acc00700 := object_fragment0361975_field_006 fuel (fragment0361975Field007Chars00 ++ (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))) fragment0361975Acc00800 := object_fragment0361975_field_007 fuel (fragment0361975Field008Chars00 ++ (fragment0361975Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0361975Field009Chars00 ++ (tail))) fragment0361975Acc00900 := object_fragment0361975_field_008 fuel (fragment0361975Field009Chars00 ++ (tail))
    _ = .ok (fragment0361975Value, tail) := object_fragment0361975_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0079_before_reader"
  err.flush

noncomputable def chunk0079LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0079SuffixChars00 : List Char := [',']
noncomputable def chunk0079Chars00 : List Char := chunk0079LeadChars00 ++ fragment0360409Chars ++ chunk0079SuffixChars00
noncomputable def chunk0079Push00 (acc : List SourceJson) : List SourceJson := fragment0360409Value :: acc

noncomputable def chunk0079AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0079_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 525)
      (SourceJson.white (chunk0079LeadChars00 ++ (fragment0360409Chars ++ rest))) acc =
      (SourceJson.value (fuel + 524) (fragment0360409Chars ++ rest)).bind
        (chunk0079AfterValue00 (fuel + 524) acc) := by rfl

theorem array_chunk0079 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 525) (SourceJson.white (chunk0079Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 524) (SourceJson.white tail) (chunk0079Push00 acc) := by
  have hinput : chunk0079Chars00 ++ tail = chunk0079LeadChars00 ++ (fragment0360409Chars ++ (chunk0079SuffixChars00 ++ tail)) := by
    simp only [chunk0079Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 525) (SourceJson.white (chunk0079Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 525)
          (SourceJson.white (chunk0079LeadChars00 ++ (fragment0360409Chars ++ (chunk0079SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 525) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 524) (fragment0360409Chars ++ (chunk0079SuffixChars00 ++ tail))).bind
        (chunk0079AfterValue00 (fuel + 524) acc) := array_chunk0079_head fuel (chunk0079SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0360409Value, chunk0079SuffixChars00 ++ tail)).bind
        (chunk0079AfterValue00 (fuel + 524) acc) :=
      congrArg (fun result => result.bind (chunk0079AfterValue00 (fuel + 524) acc))
        (value_fragment0360409 (fuel + 308) (chunk0079SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 524) (SourceJson.white tail) (chunk0079Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0079_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0080_before_reader"
  err.flush

noncomputable def chunk0080LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0080SuffixChars00 : List Char := [',']
noncomputable def chunk0080Chars00 : List Char := chunk0080LeadChars00 ++ fragment0361975Chars ++ chunk0080SuffixChars00
noncomputable def chunk0080Push00 (acc : List SourceJson) : List SourceJson := fragment0361975Value :: acc

noncomputable def chunk0080AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0080_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 524)
      (SourceJson.white (chunk0080LeadChars00 ++ (fragment0361975Chars ++ rest))) acc =
      (SourceJson.value (fuel + 523) (fragment0361975Chars ++ rest)).bind
        (chunk0080AfterValue00 (fuel + 523) acc) := by rfl

theorem array_chunk0080 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 524) (SourceJson.white (chunk0080Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 523) (SourceJson.white tail) (chunk0080Push00 acc) := by
  have hinput : chunk0080Chars00 ++ tail = chunk0080LeadChars00 ++ (fragment0361975Chars ++ (chunk0080SuffixChars00 ++ tail)) := by
    simp only [chunk0080Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 524) (SourceJson.white (chunk0080Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 524)
          (SourceJson.white (chunk0080LeadChars00 ++ (fragment0361975Chars ++ (chunk0080SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 524) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 523) (fragment0361975Chars ++ (chunk0080SuffixChars00 ++ tail))).bind
        (chunk0080AfterValue00 (fuel + 523) acc) := array_chunk0080_head fuel (chunk0080SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0361975Value, chunk0080SuffixChars00 ++ tail)).bind
        (chunk0080AfterValue00 (fuel + 523) acc) :=
      congrArg (fun result => result.bind (chunk0080AfterValue00 (fuel + 523) acc))
        (value_fragment0361975 (fuel + 319) (chunk0080SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 523) (SourceJson.white tail) (chunk0080Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0080_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0079Chars00 ++ chunk0080Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0080Push00 (chunk0079Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 525) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 523) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0079Chars00 ++ (chunk0080Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 525) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 525) (SourceJson.white (chunk0079Chars00 ++ (chunk0080Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 525) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 524) (SourceJson.white (chunk0080Chars00 ++ (tail))) (chunk0079Push00 (acc)) := array_chunk0079 fuel (chunk0080Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 523) (SourceJson.white tail) (blockPush acc) := array_chunk0080 fuel (tail) (chunk0079Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 360403).take 3126 = blockChars := by rfl

theorem block_original_split : sourceRest 360403 = blockChars ++ sourceRest 363529 := by
  calc
    sourceRest 360403 = (sourceRest 360403).take 3126 ++ (sourceRest 360403).drop 3126 :=
      (List.take_append_drop 3126 (sourceRest 360403)).symm
    _ = blockChars ++ (sourceRest 360403).drop 3126 :=
      congrArg (fun part => part ++ (sourceRest 360403).drop 3126) block_original_prefix
    _ = blockChars ++ sourceRest 363529 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 360403 3126)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 525) (SourceJson.white (sourceRest 360403)) acc =
      SourceJson.array (fuel + 523) (SourceJson.white (sourceRest 363529)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 525) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 363529) acc)

#print axioms object_fragment0360409_field_000
#print axioms object_fragment0360409_field_001
#print axioms object_fragment0360409_field_002
#print axioms object_fragment0360409_field_003
#print axioms object_fragment0360409_field_004
#print axioms object_fragment0360409_field_005
#print axioms object_fragment0360409_field_006
#print axioms object_fragment0360409_field_007
#print axioms object_fragment0360409_field_008
#print axioms object_fragment0360409_field_009
#print axioms value_fragment0360409
#print axioms object_fragment0361975_field_000
#print axioms object_fragment0361975_field_001
#print axioms object_fragment0361975_field_002
#print axioms object_fragment0361975_field_003
#print axioms object_fragment0361975_field_004
#print axioms object_fragment0361975_field_005
#print axioms object_fragment0361975_field_006
#print axioms object_fragment0361975_field_007
#print axioms object_fragment0361975_field_008
#print axioms object_fragment0361975_field_009
#print axioms value_fragment0361975
#print axioms array_chunk0079_head
#print axioms array_chunk0079
#print axioms array_chunk0080_head
#print axioms array_chunk0080
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock040

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
