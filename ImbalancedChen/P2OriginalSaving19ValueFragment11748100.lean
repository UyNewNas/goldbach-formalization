import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [117481,119096). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment117481Acc00000 : List (String × SourceJson) := []

noncomputable def fragment117481Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment117481Field000Value00 : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def fragment117481Acc00100 : List (String × SourceJson) := (fragment117481Field000Key00, fragment117481Field000Value00) :: fragment117481Acc00000
noncomputable def fragment117481Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', ',']

theorem object_fragment117481_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment117481Field000Chars00 ++ tail)) fragment117481Acc00000 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment117481Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_000"
  err.flush

noncomputable def fragment117481Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment117481Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment117481Acc00200 : List (String × SourceJson) := (fragment117481Field001Key00, fragment117481Field001Value00) :: fragment117481Acc00100
noncomputable def fragment117481Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment117481_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment117481Field001Chars00 ++ tail)) fragment117481Acc00100 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment117481Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_001"
  err.flush

noncomputable def fragment117481Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment117481Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '7', '3', '4', '3', '2', '1', '0', '5', '9', '7', '4', '7', '7', '0', '6', '0', '1', '7', '0', '7', '2', '0', '3', '7', '4', '7', '6', '3', '2', '3', '7', '6', '6', '0', '0', '5', '1', '6', '1', '6', '3', '/', '3', '6', '5', '0', '3', '1', '4', '7', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment117481Acc00300 : List (String × SourceJson) := (fragment117481Field002Key00, fragment117481Field002Value00) :: fragment117481Acc00200
noncomputable def fragment117481Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '7', '3', '4', '3', '2', '1', '0', '5', '9', '7', '4', '7', '7', '0', '6', '0', '1', '7', '0', '7', '2', '0', '3', '7', '4', '7', '6', '3', '2', '3', '7', '6', '6', '0', '0', '5', '1', '6', '1', '6', '3', '/', '3', '6', '5', '0', '3', '1', '4', '7', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment117481_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment117481Field002Chars00 ++ tail)) fragment117481Acc00200 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment117481Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_002"
  err.flush

noncomputable def fragment117481Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment117481Field003Value00 : SourceJson := .str (String.ofList ['5', '4', '6', '7', '4', '3', '/', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment117481Acc00400 : List (String × SourceJson) := (fragment117481Field003Key00, fragment117481Field003Value00) :: fragment117481Acc00300
noncomputable def fragment117481Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '4', '6', '7', '4', '3', '/', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment117481_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment117481Field003Chars00 ++ tail)) fragment117481Acc00300 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment117481Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_003"
  err.flush

noncomputable def fragment117481Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment117481Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment117481Acc00500 : List (String × SourceJson) := (fragment117481Field004Key00, fragment117481Field004Value00) :: fragment117481Acc00400
noncomputable def fragment117481Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment117481_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment117481Field004Chars00 ++ tail)) fragment117481Acc00400 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment117481Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_004"
  err.flush

noncomputable def fragment117481Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment117481Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '3', '3', '3', '1', '6', '5', '0', '2', '1', '1', '6', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '9', '0', '3', '4', '3', '4', '0', '4', '1', '0', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '4', '4', '3', '9', '1', '1', '4', '1', '5', '3', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '1', '9', '6', '2', '7', '6', '7', '0', '8', '7', '/', '1', '9', '8', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '4', '5', '3', '9', '7', '0', '2', '5', '9', '8', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '3', '8', '5', '0', '8', '8', '2', '6', '1', '4', '7', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '7', '0', '9', '7', '4', '2', '1', '7', '9', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '5', '1', '4', '6', '4', '9', '4', '1', '1', '7', '/', '1', '3', '2', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '7', '8', '3', '4', '9', '0', '4', '5', '0', '3', '/', '2', '6', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '8', '2', '1', '1', '1', '6', '0', '1', '3', '3', '/', '1', '5', '8', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment117481Acc00600 : List (String × SourceJson) := (fragment117481Field005Key00, fragment117481Field005Value00) :: fragment117481Acc00500
noncomputable def fragment117481Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '3', '3', '1', '6', '5', '0', '2', '1', '1', '6', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '9', '0', '3', '4', '3', '4', '0', '4', '1', '0', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '4', '4', '3', '9', '1', '1', '4', '1', '5', '3', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '1', '9', '6', '2', '7', '6', '7', '0', '8', '7', '/', '1', '9', '8', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '4', '5', '3', '9', '7', '0', '2', '5', '9', '8', '3', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '3', '8', '5', '0', '8', '8', '2', '6', '1', '4', '7', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '7', '0', '9', '7', '4', '2', '1', '7', '9', '/', '7', '9', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '5', '1', '4', '6', '4', '9', '4', '1', '1', '7', '/', '1', '3', '2', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '7', '8', '3', '4', '9', '0', '4', '5', '0', '3', '/', '2', '6', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '8', '2', '1', '1', '1', '6', '0', '1', '3', '3', '/', '1', '5', '8', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment117481_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment117481Field005Chars00 ++ tail)) fragment117481Acc00500 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment117481Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_005"
  err.flush

noncomputable def fragment117481Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment117481Field006Value00 : SourceJson := .str (String.ofList ['7', '4', '9', '9', '2', '9', '8', '3', '4', '9', '7', '7', '2', '4', '6', '4', '9', '0', '1', '4', '8', '4', '9', '3', '2', '1', '7', '5', '9', '8', '1', '5', '5', '3', '8', '4', '7', '3', '5', '1', '9', '3', '3', '7', '3', '8', '9', '0', '5', '6', '0', '0', '0', '0', '0', '/', '3', '3', '0', '3', '2', '0', '0', '6', '1', '0', '3', '4', '8', '5', '1', '9', '0', '9', '8', '9', '9', '2', '4', '2', '1', '3', '4', '6', '7', '8', '7', '1', '1', '8', '9', '2', '1', '0', '9', '5', '9', '4', '2', '2', '0', '7', '6', '6', '5', '0', '0', '3', '7', '6', '7', '5', '0', '4', '4', '8', '1', '7', '1', '1', '6', '4', '8', '3'])
noncomputable def fragment117481Acc00700 : List (String × SourceJson) := (fragment117481Field006Key00, fragment117481Field006Value00) :: fragment117481Acc00600
noncomputable def fragment117481Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '4', '9', '9', '2', '9', '8', '3', '4', '9', '7', '7', '2', '4', '6', '4', '9', '0', '1', '4', '8', '4', '9', '3', '2', '1', '7', '5', '9', '8', '1', '5', '5', '3', '8', '4', '7', '3', '5', '1', '9', '3', '3', '7', '3', '8', '9', '0', '5', '6', '0', '0', '0', '0', '0', '/', '3', '3', '0', '3', '2', '0', '0', '6', '1', '0', '3', '4', '8', '5', '1', '9', '0', '9', '8', '9', '9', '2', '4', '2', '1', '3', '4', '6', '7', '8', '7', '1', '1', '8', '9', '2', '1', '0', '9', '5', '9', '4', '2', '2', '0', '7', '6', '6', '5', '0', '0', '3', '7', '6', '7', '5', '0', '4', '4', '8', '1', '7', '1', '1', '6', '4', '8', '3', '"', ',']

theorem object_fragment117481_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment117481Field006Chars00 ++ tail)) fragment117481Acc00600 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment117481Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_006"
  err.flush

noncomputable def fragment117481Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment117481Field007Value00 : SourceJson := .str (String.ofList ['1', '9', '4', '9', '3', '4', '2', '1', '0', '1', '5', '9', '7', '4', '8', '9', '3', '5', '4', '1', '4', '5', '3', '0', '8', '7', '7', '2', '1', '0', '3', '7', '5', '4', '0', '3', '7', '8', '8', '0', '0', '1', '6', '5', '9', '3', '4', '4', '6', '2', '2', '8', '0', '8', '6', '5', '2', '6', '7', '3', '9', '1', '2', '8', '7', '0', '3', '8', '5', '8', '7', '0', '7', '1', '5', '1', '7', '4', '7', '8', '1', '4', '3', '1', '3', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '6', '0', '7', '2', '2', '6', '0', '2', '2', '6', '9', '0', '9', '6', '2', '6', '8', '2', '6', '6', '6', '8', '5', '2', '3', '7', '1', '0', '6', '3', '4', '1', '0', '1', '1', '2', '2', '2', '3', '1', '4', '9', '5', '1', '6', '6', '3', '9', '8', '5', '1', '3', '3', '9', '2', '0', '4', '4', '0', '7', '7', '6', '9', '7', '4', '1', '4', '7', '6', '9', '4', '8', '6', '0', '4', '1', '9', '9', '5', '8', '4', '4', '7', '8', '0', '3', '2', '6', '1', '6', '1', '5', '6', '1', '2', '6', '3', '9', '8', '0', '1', '1', '3', '6', '0', '3', '5', '8', '6', '8', '0', '4', '5', '7', '8', '5', '3', '3'])
noncomputable def fragment117481Acc00800 : List (String × SourceJson) := (fragment117481Field007Key00, fragment117481Field007Value00) :: fragment117481Acc00700
noncomputable def fragment117481Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '4', '9', '3', '4', '2', '1', '0', '1', '5', '9', '7', '4', '8', '9', '3', '5', '4', '1', '4', '5', '3', '0', '8', '7', '7', '2', '1', '0', '3', '7', '5', '4', '0', '3', '7', '8', '8', '0', '0', '1', '6', '5', '9', '3', '4', '4', '6', '2', '2', '8', '0', '8', '6', '5', '2', '6', '7', '3', '9', '1', '2', '8', '7', '0', '3', '8', '5', '8', '7', '0', '7', '1', '5', '1', '7', '4', '7', '8', '1', '4', '3', '1', '3', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '6', '0', '7', '2', '2', '6', '0', '2', '2', '6', '9', '0', '9', '6', '2', '6', '8', '2', '6', '6', '6', '8', '5', '2', '3', '7', '1', '0', '6', '3', '4', '1', '0', '1', '1', '2', '2', '2', '3', '1', '4', '9', '5', '1', '6', '6', '3', '9', '8', '5', '1', '3', '3', '9', '2', '0', '4', '4', '0', '7', '7', '6', '9', '7', '4', '1', '4', '7', '6', '9', '4', '8', '6', '0', '4', '1', '9', '9', '5', '8', '4', '4', '7', '8', '0', '3', '2', '6', '1', '6', '1', '5', '6', '1', '2', '6', '3', '9', '8', '0', '1', '1', '3', '6', '0', '3', '5', '8', '6', '8', '0', '4', '5', '7', '8', '5', '3', '3', '"', ',']

theorem object_fragment117481_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment117481Field007Chars00 ++ tail)) fragment117481Acc00700 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment117481Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_007"
  err.flush

noncomputable def fragment117481Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment117481Field008Value00 : SourceJson := .str (String.ofList ['1', '7', '9', '8', '7', '2', '7', '0', '4', '8', '3', '5', '8', '2', '2', '2', '8'])
noncomputable def fragment117481Acc00900 : List (String × SourceJson) := (fragment117481Field008Key00, fragment117481Field008Value00) :: fragment117481Acc00800
noncomputable def fragment117481Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '9', '8', '7', '2', '7', '0', '4', '8', '3', '5', '8', '2', '2', '2', '8', '"', ',']

theorem object_fragment117481_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment117481Field008Chars00 ++ tail)) fragment117481Acc00800 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment117481Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_008"
  err.flush

noncomputable def fragment117481Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment117481Field009Value00 : SourceJson := .str (String.ofList ['6', '5', '4', '2', '1', '8', '3', '0', '0', '2', '4', '7', '6', '2', '3', '5', '0'])
noncomputable def fragment117481Acc01000 : List (String × SourceJson) := (fragment117481Field009Key00, fragment117481Field009Value00) :: fragment117481Acc00900
noncomputable def fragment117481Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '4', '2', '1', '8', '3', '0', '0', '2', '4', '7', '6', '2', '3', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment117481_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment117481Field009Chars00 ++ tail)) fragment117481Acc00900 =
      .ok (.obj (fragment117481Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_object_field_009"
  err.flush

noncomputable def fragment117481Chars00 : List Char := '{' :: (fragment117481Field000Chars00 ++ fragment117481Field001Chars00 ++ fragment117481Field002Chars00 ++ fragment117481Field003Chars00 ++ fragment117481Field004Chars00 ++ fragment117481Field005Chars00 ++ fragment117481Field006Chars00 ++ fragment117481Field007Chars00 ++ fragment117481Field008Chars00 ++ fragment117481Field009Chars00)
noncomputable def fragment117481Value00 : SourceJson := .obj (fragment117481Acc01000.reverse)

theorem value_fragment117481 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 240) (fragment117481Chars00 ++ tail) =
      .ok (fragment117481Value00, tail) := by
  have hinput : fragment117481Chars00 ++ tail = '{' :: (fragment117481Field000Chars00 ++ (fragment117481Field001Chars00 ++ (fragment117481Field002Chars00 ++ (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment117481Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 240) (fragment117481Chars00 ++ tail) =
        SourceJson.value (fuel + 240) ('{' :: (fragment117481Field000Chars00 ++ (fragment117481Field001Chars00 ++ (fragment117481Field002Chars00 ++ (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 240)) hinput
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment117481Field000Chars00 ++ (fragment117481Field001Chars00 ++ (fragment117481Field002Chars00 ++ (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))))))))) fragment117481Acc00000 := by rfl
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment117481Field001Chars00 ++ (fragment117481Field002Chars00 ++ (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))))))))) fragment117481Acc00100 := object_fragment117481_field_000 fuel (fragment117481Field001Chars00 ++ (fragment117481Field002Chars00 ++ (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment117481Field002Chars00 ++ (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))))))) fragment117481Acc00200 := object_fragment117481_field_001 fuel (fragment117481Field002Chars00 ++ (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))))))) fragment117481Acc00300 := object_fragment117481_field_002 fuel (fragment117481Field003Chars00 ++ (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))))) fragment117481Acc00400 := object_fragment117481_field_003 fuel (fragment117481Field004Chars00 ++ (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))))) fragment117481Acc00500 := object_fragment117481_field_004 fuel (fragment117481Field005Chars00 ++ (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))) fragment117481Acc00600 := object_fragment117481_field_005 fuel (fragment117481Field006Chars00 ++ (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))) fragment117481Acc00700 := object_fragment117481_field_006 fuel (fragment117481Field007Chars00 ++ (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))) fragment117481Acc00800 := object_fragment117481_field_007 fuel (fragment117481Field008Chars00 ++ (fragment117481Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment117481Field009Chars00 ++ (tail))) fragment117481Acc00900 := object_fragment117481_field_008 fuel (fragment117481Field009Chars00 ++ (tail))
    _ = .ok (fragment117481Value00, tail) := object_fragment117481_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment117481_value_complete"
  err.flush

#print axioms object_fragment117481_field_000
#print axioms object_fragment117481_field_001
#print axioms object_fragment117481_field_002
#print axioms object_fragment117481_field_003
#print axioms object_fragment117481_field_004
#print axioms object_fragment117481_field_005
#print axioms object_fragment117481_field_006
#print axioms object_fragment117481_field_007
#print axioms object_fragment117481_field_008
#print axioms object_fragment117481_field_009
#print axioms value_fragment117481

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
