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

namespace SimplicesBlock006

noncomputable def fragment0246723Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0246723Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0246723Field000Value00 : SourceJson := .number (String.ofList ['1', '2'])
noncomputable def fragment0246723Acc00100 : List (String × SourceJson) := (fragment0246723Field000Key00, fragment0246723Field000Value00) :: fragment0246723Acc00000
noncomputable def fragment0246723Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', ',']

theorem object_fragment0246723_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0246723Field000Chars00 ++ tail)) fragment0246723Acc00000 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0246723Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_000"
  err.flush

noncomputable def fragment0246723Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0246723Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0246723Acc00200 : List (String × SourceJson) := (fragment0246723Field001Key00, fragment0246723Field001Value00) :: fragment0246723Acc00100
noncomputable def fragment0246723Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0246723_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0246723Field001Chars00 ++ tail)) fragment0246723Acc00100 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0246723Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_001"
  err.flush

noncomputable def fragment0246723Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0246723Field002Value00 : SourceJson := .str (String.ofList ['3', '3', '6', '1', '0', '9', '6', '8', '4', '6', '2', '0', '5', '8', '4', '9', '0', '3', '4', '0', '2', '0', '7', '9', '0', '7', '4', '9', '3', '3', '0', '0', '3', '5', '1', '/', '1', '7', '1', '1', '2', '7', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0246723Acc00300 : List (String × SourceJson) := (fragment0246723Field002Key00, fragment0246723Field002Value00) :: fragment0246723Acc00200
noncomputable def fragment0246723Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '3', '6', '1', '0', '9', '6', '8', '4', '6', '2', '0', '5', '8', '4', '9', '0', '3', '4', '0', '2', '0', '7', '9', '0', '7', '4', '9', '3', '3', '0', '0', '3', '5', '1', '/', '1', '7', '1', '1', '2', '7', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0246723_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0246723Field002Chars00 ++ tail)) fragment0246723Acc00200 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0246723Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_002"
  err.flush

noncomputable def fragment0246723Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0246723Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0246723Acc00400 : List (String × SourceJson) := (fragment0246723Field003Key00, fragment0246723Field003Value00) :: fragment0246723Acc00300
noncomputable def fragment0246723Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0246723_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0246723Field003Chars00 ++ tail)) fragment0246723Acc00300 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0246723Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_003"
  err.flush

noncomputable def fragment0246723Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0246723Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0246723Acc00500 : List (String × SourceJson) := (fragment0246723Field004Key00, fragment0246723Field004Value00) :: fragment0246723Acc00400
noncomputable def fragment0246723Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0246723_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0246723Field004Chars00 ++ tail)) fragment0246723Acc00400 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0246723Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_004"
  err.flush

noncomputable def fragment0246723Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0246723Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '5', '3', '0', '9', '7', '1', '2', '2', '1', '7', '9', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '6', '0', '3', '2', '2', '4', '4', '1', '9', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '7', '7', '3', '0', '3', '8', '8', '6', '3', '/', '8', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '2', '4', '2', '5', '1', '2', '9', '0', '9', '7', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '3', '0', '5', '8', '5', '8', '4', '5', '7', '/', '1', '3', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '9', '5', '1', '6', '9', '0', '7', '1', '4', '1', '/', '1', '1', '1', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '4', '9', '4', '5', '9', '1', '6', '2', '3', '3', '/', '8', '9', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '8', '0', '0', '6', '6', '9', '0', '1', '0', '0', '3', '/', '8', '9', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '9', '9', '0', '9', '2', '4', '5', '5', '4', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '9', '9', '0', '4', '7', '9', '0', '1', '8', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0246723Acc00600 : List (String × SourceJson) := (fragment0246723Field005Key00, fragment0246723Field005Value00) :: fragment0246723Acc00500
noncomputable def fragment0246723Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '3', '0', '9', '7', '1', '2', '2', '1', '7', '9', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '6', '0', '3', '2', '2', '4', '4', '1', '9', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '7', '7', '3', '0', '3', '8', '8', '6', '3', '/', '8', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '2', '4', '2', '5', '1', '2', '9', '0', '9', '7', '/', '7', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '3', '0', '5', '8', '5', '8', '4', '5', '7', '/', '1', '3', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '5', '1', '6', '9', '0', '7', '1', '4', '1', '/', '1', '1', '1', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '4', '9', '4', '5', '9', '1', '6', '2', '3', '3', '/', '8', '9', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '0', '0', '6', '6', '9', '0', '1', '0', '0', '3', '/', '8', '9', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '9', '9', '0', '9', '2', '4', '5', '5', '4', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '9', '9', '0', '4', '7', '9', '0', '1', '8', '7', '/', '2', '2', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0246723_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0246723Field005Chars00 ++ tail)) fragment0246723Acc00500 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0246723Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_005"
  err.flush

noncomputable def fragment0246723Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0246723Field006Value00 : SourceJson := .str (String.ofList ['3', '7', '9', '0', '3', '7', '5', '0', '8', '5', '0', '6', '0', '4', '9', '5', '6', '3', '3', '3', '1', '8', '1', '0', '3', '0', '1', '2', '3', '3', '7', '3', '5', '8', '0', '1', '7', '3', '3', '6', '0', '3', '1', '2', '5', '0', '0', '/', '3', '1', '6', '1', '2', '4', '5', '0', '8', '4', '4', '6', '5', '3', '8', '3', '2', '8', '0', '8', '0', '9', '2', '8', '8', '9', '9', '7', '2', '9', '4', '2', '2', '6', '2', '7', '4', '9', '9', '7', '1', '0', '4', '8', '0', '8', '9', '8', '5', '2', '8', '6', '1', '0', '8', '8', '2', '9', '5', '4', '6', '3'])
noncomputable def fragment0246723Acc00700 : List (String × SourceJson) := (fragment0246723Field006Key00, fragment0246723Field006Value00) :: fragment0246723Acc00600
noncomputable def fragment0246723Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '9', '0', '3', '7', '5', '0', '8', '5', '0', '6', '0', '4', '9', '5', '6', '3', '3', '3', '1', '8', '1', '0', '3', '0', '1', '2', '3', '3', '7', '3', '5', '8', '0', '1', '7', '3', '3', '6', '0', '3', '1', '2', '5', '0', '0', '/', '3', '1', '6', '1', '2', '4', '5', '0', '8', '4', '4', '6', '5', '3', '8', '3', '2', '8', '0', '8', '0', '9', '2', '8', '8', '9', '9', '7', '2', '9', '4', '2', '2', '6', '2', '7', '4', '9', '9', '7', '1', '0', '4', '8', '0', '8', '9', '8', '5', '2', '8', '6', '1', '0', '8', '8', '2', '9', '5', '4', '6', '3', '"', ',']

theorem object_fragment0246723_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0246723Field006Chars00 ++ tail)) fragment0246723Acc00600 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0246723Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_006"
  err.flush

noncomputable def fragment0246723Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0246723Field007Value00 : SourceJson := .str (String.ofList ['8', '9', '0', '1', '5', '0', '3', '7', '8', '5', '0', '1', '3', '1', '5', '4', '2', '4', '9', '2', '1', '4', '1', '8', '2', '7', '0', '6', '7', '5', '4', '6', '2', '1', '4', '4', '8', '7', '1', '2', '0', '4', '6', '5', '1', '3', '2', '9', '8', '2', '0', '7', '9', '6', '8', '6', '5', '5', '9', '0', '6', '1', '0', '7', '5', '0', '0', '8', '3', '5', '6', '5', '0', '1', '4', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '2', '8', '0', '5', '4', '2', '3', '0', '5', '4', '4', '3', '6', '1', '0', '0', '0', '0', '1', '3', '0', '9', '2', '0', '6', '2', '6', '7', '1', '6', '4', '2', '9', '7', '7', '7', '4', '3', '4', '8', '2', '5', '8', '9', '1', '8', '5', '1', '5', '4', '0', '4', '6', '7', '9', '6', '0', '3', '3', '7', '7', '4', '5', '9', '8', '1', '2', '6', '1', '6', '8', '8', '6', '6', '1', '6', '3', '2', '4', '7', '7', '0', '7', '5', '2', '7', '6', '9', '8', '5', '9', '8', '4', '1', '9', '5', '3', '2', '7', '2', '5', '7', '4', '4', '2', '6', '5', '0', '8', '3', '5', '4', '5', '1', '7', '7', '7'])
noncomputable def fragment0246723Acc00800 : List (String × SourceJson) := (fragment0246723Field007Key00, fragment0246723Field007Value00) :: fragment0246723Acc00700
noncomputable def fragment0246723Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '9', '0', '1', '5', '0', '3', '7', '8', '5', '0', '1', '3', '1', '5', '4', '2', '4', '9', '2', '1', '4', '1', '8', '2', '7', '0', '6', '7', '5', '4', '6', '2', '1', '4', '4', '8', '7', '1', '2', '0', '4', '6', '5', '1', '3', '2', '9', '8', '2', '0', '7', '9', '6', '8', '6', '5', '5', '9', '0', '6', '1', '0', '7', '5', '0', '0', '8', '3', '5', '6', '5', '0', '1', '4', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '2', '8', '0', '5', '4', '2', '3', '0', '5', '4', '4', '3', '6', '1', '0', '0', '0', '0', '1', '3', '0', '9', '2', '0', '6', '2', '6', '7', '1', '6', '4', '2', '9', '7', '7', '7', '4', '3', '4', '8', '2', '5', '8', '9', '1', '8', '5', '1', '5', '4', '0', '4', '6', '7', '9', '6', '0', '3', '3', '7', '7', '4', '5', '9', '8', '1', '2', '6', '1', '6', '8', '8', '6', '6', '1', '6', '3', '2', '4', '7', '7', '0', '7', '5', '2', '7', '6', '9', '8', '5', '9', '8', '4', '1', '9', '5', '3', '2', '7', '2', '5', '7', '4', '4', '2', '6', '5', '0', '8', '3', '5', '4', '5', '1', '7', '7', '7', '"', ',']

theorem object_fragment0246723_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0246723Field007Chars00 ++ tail)) fragment0246723Acc00700 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0246723Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_007"
  err.flush

noncomputable def fragment0246723Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0246723Field008Value00 : SourceJson := .str (String.ofList ['9', '4', '9', '9', '5', '6', '2', '5', '2', '0', '6', '3', '1', '8'])
noncomputable def fragment0246723Acc00900 : List (String × SourceJson) := (fragment0246723Field008Key00, fragment0246723Field008Value00) :: fragment0246723Acc00800
noncomputable def fragment0246723Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '4', '9', '9', '5', '6', '2', '5', '2', '0', '6', '3', '1', '8', '"', ',']

theorem object_fragment0246723_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0246723Field008Chars00 ++ tail)) fragment0246723Acc00800 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0246723Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_008"
  err.flush

noncomputable def fragment0246723Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0246723Field009Value00 : SourceJson := .str (String.ofList ['6', '2', '5', '1', '9', '1', '3', '8', '6', '5', '5', '2', '4', '2', '7'])
noncomputable def fragment0246723Acc01000 : List (String × SourceJson) := (fragment0246723Field009Key00, fragment0246723Field009Value00) :: fragment0246723Acc00900
noncomputable def fragment0246723Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '2', '5', '1', '9', '1', '3', '8', '6', '5', '5', '2', '4', '2', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0246723_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0246723Field009Chars00 ++ tail)) fragment0246723Acc00900 =
      .ok (.obj (fragment0246723Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0246723_object_field_009"
  err.flush

noncomputable def fragment0246723Chars : List Char := '{' :: (fragment0246723Field000Chars00 ++ fragment0246723Field001Chars00 ++ fragment0246723Field002Chars00 ++ fragment0246723Field003Chars00 ++ fragment0246723Field004Chars00 ++ fragment0246723Field005Chars00 ++ fragment0246723Field006Chars00 ++ fragment0246723Field007Chars00 ++ fragment0246723Field008Chars00 ++ fragment0246723Field009Chars00)
noncomputable def fragment0246723Value : SourceJson := .obj (fragment0246723Acc01000.reverse)

theorem value_fragment0246723 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 235) (fragment0246723Chars ++ tail) =
      .ok (fragment0246723Value, tail) := by
  have hinput : fragment0246723Chars ++ tail = '{' :: (fragment0246723Field000Chars00 ++ (fragment0246723Field001Chars00 ++ (fragment0246723Field002Chars00 ++ (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0246723Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 235) (fragment0246723Chars ++ tail) =
        SourceJson.value (fuel + 235) ('{' :: (fragment0246723Field000Chars00 ++ (fragment0246723Field001Chars00 ++ (fragment0246723Field002Chars00 ++ (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 235)) hinput
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0246723Field000Chars00 ++ (fragment0246723Field001Chars00 ++ (fragment0246723Field002Chars00 ++ (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))))))))) fragment0246723Acc00000 := by rfl
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0246723Field001Chars00 ++ (fragment0246723Field002Chars00 ++ (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))))))))) fragment0246723Acc00100 := object_fragment0246723_field_000 fuel (fragment0246723Field001Chars00 ++ (fragment0246723Field002Chars00 ++ (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0246723Field002Chars00 ++ (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))))))) fragment0246723Acc00200 := object_fragment0246723_field_001 fuel (fragment0246723Field002Chars00 ++ (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))))))) fragment0246723Acc00300 := object_fragment0246723_field_002 fuel (fragment0246723Field003Chars00 ++ (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))))) fragment0246723Acc00400 := object_fragment0246723_field_003 fuel (fragment0246723Field004Chars00 ++ (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))))) fragment0246723Acc00500 := object_fragment0246723_field_004 fuel (fragment0246723Field005Chars00 ++ (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))) fragment0246723Acc00600 := object_fragment0246723_field_005 fuel (fragment0246723Field006Chars00 ++ (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))) fragment0246723Acc00700 := object_fragment0246723_field_006 fuel (fragment0246723Field007Chars00 ++ (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))) fragment0246723Acc00800 := object_fragment0246723_field_007 fuel (fragment0246723Field008Chars00 ++ (fragment0246723Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0246723Field009Chars00 ++ (tail))) fragment0246723Acc00900 := object_fragment0246723_field_008 fuel (fragment0246723Field009Chars00 ++ (tail))
    _ = .ok (fragment0246723Value, tail) := object_fragment0246723_field_009 fuel (tail)

noncomputable def fragment0248296Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0248296Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0248296Field000Value00 : SourceJson := .number (String.ofList ['1', '3'])
noncomputable def fragment0248296Acc00100 : List (String × SourceJson) := (fragment0248296Field000Key00, fragment0248296Field000Value00) :: fragment0248296Acc00000
noncomputable def fragment0248296Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', ',']

theorem object_fragment0248296_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0248296Field000Chars00 ++ tail)) fragment0248296Acc00000 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0248296Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_000"
  err.flush

noncomputable def fragment0248296Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0248296Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0248296Acc00200 : List (String × SourceJson) := (fragment0248296Field001Key00, fragment0248296Field001Value00) :: fragment0248296Acc00100
noncomputable def fragment0248296Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0248296_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0248296Field001Chars00 ++ tail)) fragment0248296Acc00100 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0248296Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_001"
  err.flush

noncomputable def fragment0248296Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0248296Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '6', '1', '0', '8', '1', '1', '2', '7', '5', '2', '2', '4', '8', '5', '1', '9', '5', '3', '7', '3', '3', '5', '5', '1', '5', '0', '4', '5', '7', '1', '7', '3', '5', '0', '8', '2', '3', '9', '/', '1', '0', '2', '6', '7', '6', '5', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0248296Acc00300 : List (String × SourceJson) := (fragment0248296Field002Key00, fragment0248296Field002Value00) :: fragment0248296Acc00200
noncomputable def fragment0248296Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '6', '1', '0', '8', '1', '1', '2', '7', '5', '2', '2', '4', '8', '5', '1', '9', '5', '3', '7', '3', '3', '5', '5', '1', '5', '0', '4', '5', '7', '1', '7', '3', '5', '0', '8', '2', '3', '9', '/', '1', '0', '2', '6', '7', '6', '5', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0248296_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0248296Field002Chars00 ++ tail)) fragment0248296Acc00200 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0248296Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_002"
  err.flush

noncomputable def fragment0248296Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0248296Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0'])
noncomputable def fragment0248296Acc00400 : List (String × SourceJson) := (fragment0248296Field003Key00, fragment0248296Field003Value00) :: fragment0248296Acc00300
noncomputable def fragment0248296Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0', '"', ',']

theorem object_fragment0248296_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0248296Field003Chars00 ++ tail)) fragment0248296Acc00300 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0248296Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_003"
  err.flush

noncomputable def fragment0248296Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0248296Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0248296Acc00500 : List (String × SourceJson) := (fragment0248296Field004Key00, fragment0248296Field004Value00) :: fragment0248296Acc00400
noncomputable def fragment0248296Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '5', '0', '7', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0248296_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0248296Field004Chars00 ++ tail)) fragment0248296Acc00400 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0248296Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_004"
  err.flush

noncomputable def fragment0248296Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0248296Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '6', '7', '0', '3', '7', '6', '4', '3', '5', '7', '5', '6', '1', '8', '9', '/', '2', '8', '4', '8', '3', '0', '8', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '0', '8', '9', '0', '6', '4', '2', '4', '8', '1', '7', '8', '2', '4', '3', '7', '/', '2', '7', '9', '1', '3', '4', '2', '8', '1', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '9', '5', '2', '6', '1', '8', '6', '9', '5', '1', '8', '2', '0', '7', '3', '1', '/', '1', '2', '8', '8', '3', '1', '2', '0', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '2', '3', '3', '5', '4', '0', '0', '6', '2', '9', '4', '7', '4', '4', '1', '8', '7', '/', '5', '5', '8', '2', '6', '8', '5', '6', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '5', '5', '3', '2', '1', '6', '5', '1', '4', '6', '3', '2', '0', '0', '3', '/', '2', '4', '6', '2', '9', '4', '9', '5', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '3', '7', '8', '5', '4', '5', '0', '7', '6', '6', '0', '6', '4', '3', '2', '7', '7', '/', '1', '6', '7', '4', '8', '0', '5', '6', '8', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '5', '8', '8', '8', '8', '0', '4', '8', '6', '4', '2', '3', '4', '2', '6', '9', '3', '/', '6', '6', '9', '9', '2', '2', '2', '7', '5', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '6', '8', '9', '3', '7', '8', '4', '6', '6', '2', '1', '7', '5', '0', '6', '6', '3', '/', '6', '6', '9', '9', '2', '2', '2', '7', '5', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '5', '2', '9', '5', '0', '1', '4', '8', '7', '5', '8', '7', '3', '7', '1', '3', '/', '4', '1', '8', '7', '0', '1', '4', '2', '2', '4', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '6', '2', '1', '9', '1', '9', '6', '9', '7', '9', '7', '3', '8', '7', '6', '1', '/', '8', '3', '7', '4', '0', '2', '8', '4', '4', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0248296Acc00600 : List (String × SourceJson) := (fragment0248296Field005Key00, fragment0248296Field005Value00) :: fragment0248296Acc00500
noncomputable def fragment0248296Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '7', '0', '3', '7', '6', '4', '3', '5', '7', '5', '6', '1', '8', '9', '/', '2', '8', '4', '8', '3', '0', '8', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '0', '8', '9', '0', '6', '4', '2', '4', '8', '1', '7', '8', '2', '4', '3', '7', '/', '2', '7', '9', '1', '3', '4', '2', '8', '1', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '9', '5', '2', '6', '1', '8', '6', '9', '5', '1', '8', '2', '0', '7', '3', '1', '/', '1', '2', '8', '8', '3', '1', '2', '0', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '2', '3', '3', '5', '4', '0', '0', '6', '2', '9', '4', '7', '4', '4', '1', '8', '7', '/', '5', '5', '8', '2', '6', '8', '5', '6', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '5', '5', '3', '2', '1', '6', '5', '1', '4', '6', '3', '2', '0', '0', '3', '/', '2', '4', '6', '2', '9', '4', '9', '5', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '3', '7', '8', '5', '4', '5', '0', '7', '6', '6', '0', '6', '4', '3', '2', '7', '7', '/', '1', '6', '7', '4', '8', '0', '5', '6', '8', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '5', '8', '8', '8', '8', '0', '4', '8', '6', '4', '2', '3', '4', '2', '6', '9', '3', '/', '6', '6', '9', '9', '2', '2', '2', '7', '5', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '6', '8', '9', '3', '7', '8', '4', '6', '6', '2', '1', '7', '5', '0', '6', '6', '3', '/', '6', '6', '9', '9', '2', '2', '2', '7', '5', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '5', '2', '9', '5', '0', '1', '4', '8', '7', '5', '8', '7', '3', '7', '1', '3', '/', '4', '1', '8', '7', '0', '1', '4', '2', '2', '4', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '6', '2', '1', '9', '1', '9', '6', '9', '7', '9', '7', '3', '8', '7', '6', '1', '/', '8', '3', '7', '4', '0', '2', '8', '4', '4', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0248296_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0248296Field005Chars00 ++ tail)) fragment0248296Acc00500 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0248296Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_005"
  err.flush

noncomputable def fragment0248296Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0248296Field006Value00 : SourceJson := .str (String.ofList ['3', '6', '6', '3', '0', '8', '2', '0', '7', '9', '4', '3', '7', '7', '6', '3', '9', '4', '7', '4', '6', '9', '3', '9', '0', '4', '1', '7', '4', '4', '1', '1', '3', '7', '0', '5', '9', '1', '2', '6', '5', '6', '4', '0', '9', '7', '5', '0', '0', '0', '0', '0', '/', '2', '8', '4', '5', '1', '0', '2', '2', '5', '2', '4', '9', '0', '5', '6', '5', '5', '7', '1', '2', '1', '4', '1', '2', '8', '0', '4', '2', '5', '8', '5', '7', '5', '4', '3', '7', '1', '0', '2', '3', '4', '3', '2', '8', '5', '7', '0', '8', '7', '3', '7', '3', '3', '0', '4', '6', '4', '4', '5', '8', '4', '4', '7'])
noncomputable def fragment0248296Acc00700 : List (String × SourceJson) := (fragment0248296Field006Key00, fragment0248296Field006Value00) :: fragment0248296Acc00600
noncomputable def fragment0248296Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '6', '6', '3', '0', '8', '2', '0', '7', '9', '4', '3', '7', '7', '6', '3', '9', '4', '7', '4', '6', '9', '3', '9', '0', '4', '1', '7', '4', '4', '1', '1', '3', '7', '0', '5', '9', '1', '2', '6', '5', '6', '4', '0', '9', '7', '5', '0', '0', '0', '0', '0', '/', '2', '8', '4', '5', '1', '0', '2', '2', '5', '2', '4', '9', '0', '5', '6', '5', '5', '7', '1', '2', '1', '4', '1', '2', '8', '0', '4', '2', '5', '8', '5', '7', '5', '4', '3', '7', '1', '0', '2', '3', '4', '3', '2', '8', '5', '7', '0', '8', '7', '3', '7', '3', '3', '0', '4', '6', '4', '4', '5', '8', '4', '4', '7', '"', ',']

theorem object_fragment0248296_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0248296Field006Chars00 ++ tail)) fragment0248296Acc00600 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0248296Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_006"
  err.flush

noncomputable def fragment0248296Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0248296Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '5', '8', '4', '3', '1', '6', '6', '9', '9', '1', '1', '7', '1', '6', '4', '5', '4', '6', '2', '4', '5', '9', '0', '2', '0', '6', '8', '8', '7', '1', '8', '2', '4', '4', '4', '3', '5', '9', '1', '5', '8', '3', '8', '8', '1', '3', '6', '9', '8', '6', '0', '9', '8', '4', '8', '9', '9', '0', '0', '1', '5', '0', '8', '8', '6', '9', '1', '8', '1', '4', '8', '5', '2', '7', '3', '3', '3', '3', '8', '0', '3', '4', '0', '4', '3', '8', '2', '6', '4', '6', '0', '8', '8', '0', '5', '8', '0', '6', '2', '3', '3', '8', '2', '5', '8', '0', '5', '0', '0', '5', '3', '2', '9', '8', '5', '3', '0', '5', '6', '5', '5', '8', '3', '1', '2', '8', '2', '8', '4', '5', '0', '9', '0', '4', '3', '6', '1', '2', '1', '0', '8', '4', '2', '3', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '1', '4', '0', '5', '7', '7', '9', '7', '0', '0', '5', '8', '9', '5', '0', '5', '5', '3', '4', '9', '9', '5', '1', '5', '7', '6', '1', '9', '1', '0', '5', '4', '3', '8', '5', '8', '9', '1', '9', '6', '2', '2', '3', '9', '7', '8', '3', '2', '8', '9', '9', '9', '8', '1', '3', '5', '1', '9', '4', '6', '3', '9', '2', '4', '3', '6', '7', '8', '7', '9', '1', '3', '8', '6', '6', '4', '5', '4', '7', '4', '5', '3', '9', '6', '5', '5', '7', '9', '8', '0', '8', '9', '6', '9', '5', '0', '0', '5', '8', '4', '6', '8', '6', '4', '0', '3', '5', '8', '5', '0', '4', '2', '6', '6', '7', '7', '1', '4', '9', '3', '9', '4', '5', '7', '3', '2', '4', '5', '4', '5', '7', '0', '3', '1', '2', '6', '9', '6', '7', '0', '4', '8', '0', '1', '8', '3', '6', '8', '5', '0', '1', '7', '8', '2', '8', '0', '0', '1', '9', '8', '0', '4', '1', '1', '7', '4', '8', '8', '2', '6', '1', '7', '0', '1', '1', '7', '4', '0', '0', '4', '3', '7'])
noncomputable def fragment0248296Acc00800 : List (String × SourceJson) := (fragment0248296Field007Key00, fragment0248296Field007Value00) :: fragment0248296Acc00700
noncomputable def fragment0248296Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '5', '8', '4', '3', '1', '6', '6', '9', '9', '1', '1', '7', '1', '6', '4', '5', '4', '6', '2', '4', '5', '9', '0', '2', '0', '6', '8', '8', '7', '1', '8', '2', '4', '4', '4', '3', '5', '9', '1', '5', '8', '3', '8', '8', '1', '3', '6', '9', '8', '6', '0', '9', '8', '4', '8', '9', '9', '0', '0', '1', '5', '0', '8', '8', '6', '9', '1', '8', '1', '4', '8', '5', '2', '7', '3', '3', '3', '3', '8', '0', '3', '4', '0', '4', '3', '8', '2', '6', '4', '6', '0', '8', '8', '0', '5', '8', '0', '6', '2', '3', '3', '8', '2', '5', '8', '0', '5', '0', '0', '5', '3', '2', '9', '8', '5', '3', '0', '5', '6', '5', '5', '8', '3', '1', '2', '8', '2', '8', '4', '5', '0', '9', '0', '4', '3', '6', '1', '2', '1', '0', '8', '4', '2', '3', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '1', '4', '0', '5', '7', '7', '9', '7', '0', '0', '5', '8', '9', '5', '0', '5', '5', '3', '4', '9', '9', '5', '1', '5', '7', '6', '1', '9', '1', '0', '5', '4', '3', '8', '5', '8', '9', '1', '9', '6', '2', '2', '3', '9', '7', '8', '3', '2', '8', '9', '9', '9', '8', '1', '3', '5', '1', '9', '4', '6', '3', '9', '2', '4', '3', '6', '7', '8', '7', '9', '1', '3', '8', '6', '6', '4', '5', '4', '7', '4', '5', '3', '9', '6', '5', '5', '7', '9', '8', '0', '8', '9', '6', '9', '5', '0', '0', '5', '8', '4', '6', '8', '6', '4', '0', '3', '5', '8', '5', '0', '4', '2', '6', '6', '7', '7', '1', '4', '9', '3', '9', '4', '5', '7', '3', '2', '4', '5', '4', '5', '7', '0', '3', '1', '2', '6', '9', '6', '7', '0', '4', '8', '0', '1', '8', '3', '6', '8', '5', '0', '1', '7', '8', '2', '8', '0', '0', '1', '9', '8', '0', '4', '1', '1', '7', '4', '8', '8', '2', '6', '1', '7', '0', '1', '1', '7', '4', '0', '0', '4', '3', '7', '"', ',']

theorem object_fragment0248296_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0248296Field007Chars00 ++ tail)) fragment0248296Acc00700 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0248296Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_007"
  err.flush

noncomputable def fragment0248296Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0248296Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '2', '0', '0', '6', '6', '1', '9', '2', '8', '3', '6', '2', '3', '4', '0', '4', '4'])
noncomputable def fragment0248296Acc00900 : List (String × SourceJson) := (fragment0248296Field008Key00, fragment0248296Field008Value00) :: fragment0248296Acc00800
noncomputable def fragment0248296Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '2', '0', '0', '6', '6', '1', '9', '2', '8', '3', '6', '2', '3', '4', '0', '4', '4', '"', ',']

theorem object_fragment0248296_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0248296Field008Chars00 ++ tail)) fragment0248296Acc00800 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0248296Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_008"
  err.flush

noncomputable def fragment0248296Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0248296Field009Value00 : SourceJson := .str (String.ofList ['6', '9', '1', '7', '2', '4', '4', '8', '9', '3', '4', '2', '3', '8', '2', '6', '5', '7', '9'])
noncomputable def fragment0248296Acc01000 : List (String × SourceJson) := (fragment0248296Field009Key00, fragment0248296Field009Value00) :: fragment0248296Acc00900
noncomputable def fragment0248296Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '1', '7', '2', '4', '4', '8', '9', '3', '4', '2', '3', '8', '2', '6', '5', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0248296_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0248296Field009Chars00 ++ tail)) fragment0248296Acc00900 =
      .ok (.obj (fragment0248296Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0248296_object_field_009"
  err.flush

noncomputable def fragment0248296Chars : List Char := '{' :: (fragment0248296Field000Chars00 ++ fragment0248296Field001Chars00 ++ fragment0248296Field002Chars00 ++ fragment0248296Field003Chars00 ++ fragment0248296Field004Chars00 ++ fragment0248296Field005Chars00 ++ fragment0248296Field006Chars00 ++ fragment0248296Field007Chars00 ++ fragment0248296Field008Chars00 ++ fragment0248296Field009Chars00)
noncomputable def fragment0248296Value : SourceJson := .obj (fragment0248296Acc01000.reverse)

theorem value_fragment0248296 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 370) (fragment0248296Chars ++ tail) =
      .ok (fragment0248296Value, tail) := by
  have hinput : fragment0248296Chars ++ tail = '{' :: (fragment0248296Field000Chars00 ++ (fragment0248296Field001Chars00 ++ (fragment0248296Field002Chars00 ++ (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0248296Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 370) (fragment0248296Chars ++ tail) =
        SourceJson.value (fuel + 370) ('{' :: (fragment0248296Field000Chars00 ++ (fragment0248296Field001Chars00 ++ (fragment0248296Field002Chars00 ++ (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 370)) hinput
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0248296Field000Chars00 ++ (fragment0248296Field001Chars00 ++ (fragment0248296Field002Chars00 ++ (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))))))))) fragment0248296Acc00000 := by rfl
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0248296Field001Chars00 ++ (fragment0248296Field002Chars00 ++ (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))))))))) fragment0248296Acc00100 := object_fragment0248296_field_000 fuel (fragment0248296Field001Chars00 ++ (fragment0248296Field002Chars00 ++ (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0248296Field002Chars00 ++ (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))))))) fragment0248296Acc00200 := object_fragment0248296_field_001 fuel (fragment0248296Field002Chars00 ++ (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))))))) fragment0248296Acc00300 := object_fragment0248296_field_002 fuel (fragment0248296Field003Chars00 ++ (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))))) fragment0248296Acc00400 := object_fragment0248296_field_003 fuel (fragment0248296Field004Chars00 ++ (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))))) fragment0248296Acc00500 := object_fragment0248296_field_004 fuel (fragment0248296Field005Chars00 ++ (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))) fragment0248296Acc00600 := object_fragment0248296_field_005 fuel (fragment0248296Field006Chars00 ++ (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))) fragment0248296Acc00700 := object_fragment0248296_field_006 fuel (fragment0248296Field007Chars00 ++ (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))) fragment0248296Acc00800 := object_fragment0248296_field_007 fuel (fragment0248296Field008Chars00 ++ (fragment0248296Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0248296Field009Chars00 ++ (tail))) fragment0248296Acc00900 := object_fragment0248296_field_008 fuel (fragment0248296Field009Chars00 ++ (tail))
    _ = .ok (fragment0248296Value, tail) := object_fragment0248296_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_before_reader"
  err.flush

noncomputable def chunk0012LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0012SuffixChars00 : List Char := [',']
noncomputable def chunk0012Chars00 : List Char := chunk0012LeadChars00 ++ fragment0246723Chars ++ chunk0012SuffixChars00
noncomputable def chunk0012Push00 (acc : List SourceJson) : List SourceJson := fragment0246723Value :: acc

noncomputable def chunk0012AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0012_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 592)
      (SourceJson.white (chunk0012LeadChars00 ++ (fragment0246723Chars ++ rest))) acc =
      (SourceJson.value (fuel + 591) (fragment0246723Chars ++ rest)).bind
        (chunk0012AfterValue00 (fuel + 591) acc) := by rfl

theorem array_chunk0012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 592) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 591) (SourceJson.white tail) (chunk0012Push00 acc) := by
  have hinput : chunk0012Chars00 ++ tail = chunk0012LeadChars00 ++ (fragment0246723Chars ++ (chunk0012SuffixChars00 ++ tail)) := by
    simp only [chunk0012Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 592) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 592)
          (SourceJson.white (chunk0012LeadChars00 ++ (fragment0246723Chars ++ (chunk0012SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 592) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 591) (fragment0246723Chars ++ (chunk0012SuffixChars00 ++ tail))).bind
        (chunk0012AfterValue00 (fuel + 591) acc) := array_chunk0012_head fuel (chunk0012SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0246723Value, chunk0012SuffixChars00 ++ tail)).bind
        (chunk0012AfterValue00 (fuel + 591) acc) :=
      congrArg (fun result => result.bind (chunk0012AfterValue00 (fuel + 591) acc))
        (value_fragment0246723 (fuel + 356) (chunk0012SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 591) (SourceJson.white tail) (chunk0012Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_before_reader"
  err.flush

noncomputable def chunk0013LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0013SuffixChars00 : List Char := [',']
noncomputable def chunk0013Chars00 : List Char := chunk0013LeadChars00 ++ fragment0248296Chars ++ chunk0013SuffixChars00
noncomputable def chunk0013Push00 (acc : List SourceJson) : List SourceJson := fragment0248296Value :: acc

noncomputable def chunk0013AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0013_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 591)
      (SourceJson.white (chunk0013LeadChars00 ++ (fragment0248296Chars ++ rest))) acc =
      (SourceJson.value (fuel + 590) (fragment0248296Chars ++ rest)).bind
        (chunk0013AfterValue00 (fuel + 590) acc) := by rfl

theorem array_chunk0013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 591) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 590) (SourceJson.white tail) (chunk0013Push00 acc) := by
  have hinput : chunk0013Chars00 ++ tail = chunk0013LeadChars00 ++ (fragment0248296Chars ++ (chunk0013SuffixChars00 ++ tail)) := by
    simp only [chunk0013Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 591) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 591)
          (SourceJson.white (chunk0013LeadChars00 ++ (fragment0248296Chars ++ (chunk0013SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 591) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 590) (fragment0248296Chars ++ (chunk0013SuffixChars00 ++ tail))).bind
        (chunk0013AfterValue00 (fuel + 590) acc) := array_chunk0013_head fuel (chunk0013SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0248296Value, chunk0013SuffixChars00 ++ tail)).bind
        (chunk0013AfterValue00 (fuel + 590) acc) :=
      congrArg (fun result => result.bind (chunk0013AfterValue00 (fuel + 590) acc))
        (value_fragment0248296 (fuel + 220) (chunk0013SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 590) (SourceJson.white tail) (chunk0013Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0012Chars00 ++ chunk0013Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0013Push00 (chunk0012Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 592) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 590) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0012Chars00 ++ (chunk0013Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 592) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 592) (SourceJson.white (chunk0012Chars00 ++ (chunk0013Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 592) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 591) (SourceJson.white (chunk0013Chars00 ++ (tail))) (chunk0012Push00 (acc)) := array_chunk0012 fuel (chunk0013Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 590) (SourceJson.white tail) (blockPush acc) := array_chunk0013 fuel (tail) (chunk0012Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 246717).take 3442 = blockChars := by rfl

theorem block_original_split : sourceRest 246717 = blockChars ++ sourceRest 250159 := by
  calc
    sourceRest 246717 = (sourceRest 246717).take 3442 ++ (sourceRest 246717).drop 3442 :=
      (List.take_append_drop 3442 (sourceRest 246717)).symm
    _ = blockChars ++ (sourceRest 246717).drop 3442 :=
      congrArg (fun part => part ++ (sourceRest 246717).drop 3442) block_original_prefix
    _ = blockChars ++ sourceRest 250159 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 246717 3442)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 592) (SourceJson.white (sourceRest 246717)) acc =
      SourceJson.array (fuel + 590) (SourceJson.white (sourceRest 250159)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 592) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 250159) acc)

#print axioms object_fragment0246723_field_000
#print axioms object_fragment0246723_field_001
#print axioms object_fragment0246723_field_002
#print axioms object_fragment0246723_field_003
#print axioms object_fragment0246723_field_004
#print axioms object_fragment0246723_field_005
#print axioms object_fragment0246723_field_006
#print axioms object_fragment0246723_field_007
#print axioms object_fragment0246723_field_008
#print axioms object_fragment0246723_field_009
#print axioms value_fragment0246723
#print axioms object_fragment0248296_field_000
#print axioms object_fragment0248296_field_001
#print axioms object_fragment0248296_field_002
#print axioms object_fragment0248296_field_003
#print axioms object_fragment0248296_field_004
#print axioms object_fragment0248296_field_005
#print axioms object_fragment0248296_field_006
#print axioms object_fragment0248296_field_007
#print axioms object_fragment0248296_field_008
#print axioms object_fragment0248296_field_009
#print axioms value_fragment0248296
#print axioms array_chunk0012_head
#print axioms array_chunk0012
#print axioms array_chunk0013_head
#print axioms array_chunk0013
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock006

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
