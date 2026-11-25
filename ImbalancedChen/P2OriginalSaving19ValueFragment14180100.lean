import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [141801,143415). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment141801Acc00000 : List (String × SourceJson) := []

noncomputable def fragment141801Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment141801Field000Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment141801Acc00100 : List (String × SourceJson) := (fragment141801Field000Key00, fragment141801Field000Value00) :: fragment141801Acc00000
noncomputable def fragment141801Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '4', ',']

theorem object_fragment141801_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment141801Field000Chars00 ++ tail)) fragment141801Acc00000 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment141801Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_000"
  err.flush

noncomputable def fragment141801Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment141801Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment141801Acc00200 : List (String × SourceJson) := (fragment141801Field001Key00, fragment141801Field001Value00) :: fragment141801Acc00100
noncomputable def fragment141801Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment141801_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment141801Field001Chars00 ++ tail)) fragment141801Acc00100 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment141801Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_001"
  err.flush

noncomputable def fragment141801Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment141801Field002Value00 : SourceJson := .str (String.ofList ['6', '8', '4', '2', '7', '6', '8', '6', '1', '3', '4', '0', '5', '7', '8', '2', '5', '0', '5', '8', '4', '5', '3', '9', '3', '1', '8', '6', '7', '3', '0', '2', '9', '2', '7', '/', '6', '0', '1', '8', '8', '6', '1', '8', '0', '2', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment141801Acc00300 : List (String × SourceJson) := (fragment141801Field002Key00, fragment141801Field002Value00) :: fragment141801Acc00200
noncomputable def fragment141801Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '8', '4', '2', '7', '6', '8', '6', '1', '3', '4', '0', '5', '7', '8', '2', '5', '0', '5', '8', '4', '5', '3', '9', '3', '1', '8', '6', '7', '3', '0', '2', '9', '2', '7', '/', '6', '0', '1', '8', '8', '6', '1', '8', '0', '2', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment141801_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment141801Field002Chars00 ++ tail)) fragment141801Acc00200 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment141801Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_002"
  err.flush

noncomputable def fragment141801Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment141801Field003Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '0', '2', '6', '9', '/', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment141801Acc00400 : List (String × SourceJson) := (fragment141801Field003Key00, fragment141801Field003Value00) :: fragment141801Acc00300
noncomputable def fragment141801Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '6', '4', '0', '2', '6', '9', '/', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment141801_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment141801Field003Chars00 ++ tail)) fragment141801Acc00300 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment141801Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_003"
  err.flush

noncomputable def fragment141801Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment141801Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment141801Acc00500 : List (String × SourceJson) := (fragment141801Field004Key00, fragment141801Field004Value00) :: fragment141801Acc00400
noncomputable def fragment141801Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment141801_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment141801Field004Chars00 ++ tail)) fragment141801Acc00400 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment141801Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_004"
  err.flush

noncomputable def fragment141801Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment141801Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '3', '1', '1', '0', '8', '5', '6', '5', '2', '5', '8', '3', '/', '1', '3', '6', '9', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '0', '9', '5', '3', '6', '3', '8', '1', '0', '9', '9', '/', '6', '8', '4', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '7', '4', '6', '3', '7', '2', '1', '6', '7', '/', '6', '0', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '1', '8', '7', '8', '3', '2', '5', '0', '2', '3', '/', '1', '0', '5', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '6', '0', '8', '6', '1', '7', '8', '6', '7', '7', '7', '/', '4', '5', '6', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '7', '9', '7', '3', '7', '7', '5', '1', '9', '/', '3', '0', '4', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '2', '1', '8', '7', '7', '1', '1', '1', '9', '/', '3', '8', '0', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '5', '4', '4', '7', '1', '3', '4', '7', '5', '9', '/', '3', '4', '2', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '4', '6', '1', '8', '7', '4', '8', '5', '9', '9', '/', '3', '4', '2', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '7', '3', '8', '1', '8', '0', '2', '5', '5', '3', '/', '6', '8', '4', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment141801Acc00600 : List (String × SourceJson) := (fragment141801Field005Key00, fragment141801Field005Value00) :: fragment141801Acc00500
noncomputable def fragment141801Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '1', '1', '0', '8', '5', '6', '5', '2', '5', '8', '3', '/', '1', '3', '6', '9', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '0', '9', '5', '3', '6', '3', '8', '1', '0', '9', '9', '/', '6', '8', '4', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '7', '4', '6', '3', '7', '2', '1', '6', '7', '/', '6', '0', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '1', '8', '7', '8', '3', '2', '5', '0', '2', '3', '/', '1', '0', '5', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '6', '0', '8', '6', '1', '7', '8', '6', '7', '7', '7', '/', '4', '5', '6', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '7', '9', '7', '3', '7', '7', '5', '1', '9', '/', '3', '0', '4', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '2', '1', '8', '7', '7', '1', '1', '1', '9', '/', '3', '8', '0', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '5', '4', '4', '7', '1', '3', '4', '7', '5', '9', '/', '3', '4', '2', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '4', '6', '1', '8', '7', '4', '8', '5', '9', '9', '/', '3', '4', '2', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '7', '3', '8', '1', '8', '0', '2', '5', '5', '3', '/', '6', '8', '4', '6', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment141801_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment141801Field005Chars00 ++ tail)) fragment141801Acc00500 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment141801Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_005"
  err.flush

noncomputable def fragment141801Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment141801Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '6', '8', '3', '8', '7', '0', '6', '6', '2', '2', '7', '0', '2', '3', '5', '6', '1', '7', '7', '4', '4', '5', '8', '0', '4', '9', '6', '1', '0', '2', '9', '1', '5', '9', '6', '5', '7', '4', '5', '8', '4', '9', '2', '5', '0', '6', '1', '1', '2', '0', '0', '0', '0', '0', '0', '/', '1', '2', '7', '4', '8', '9', '6', '8', '1', '2', '6', '6', '0', '1', '7', '0', '8', '1', '4', '8', '1', '7', '2', '4', '3', '4', '3', '1', '4', '8', '8', '1', '5', '8', '3', '0', '7', '8', '5', '0', '6', '8', '7', '3', '3', '2', '6', '7', '9', '4', '5', '8', '5', '7', '2', '6', '1', '7', '9', '6', '6', '2', '5', '0', '0', '2', '0', '8', '9', '1'])
noncomputable def fragment141801Acc00700 : List (String × SourceJson) := (fragment141801Field006Key00, fragment141801Field006Value00) :: fragment141801Acc00600
noncomputable def fragment141801Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '6', '8', '3', '8', '7', '0', '6', '6', '2', '2', '7', '0', '2', '3', '5', '6', '1', '7', '7', '4', '4', '5', '8', '0', '4', '9', '6', '1', '0', '2', '9', '1', '5', '9', '6', '5', '7', '4', '5', '8', '4', '9', '2', '5', '0', '6', '1', '1', '2', '0', '0', '0', '0', '0', '0', '/', '1', '2', '7', '4', '8', '9', '6', '8', '1', '2', '6', '6', '0', '1', '7', '0', '8', '1', '4', '8', '1', '7', '2', '4', '3', '4', '3', '1', '4', '8', '8', '1', '5', '8', '3', '0', '7', '8', '5', '0', '6', '8', '7', '3', '3', '2', '6', '7', '9', '4', '5', '8', '5', '7', '2', '6', '1', '7', '9', '6', '6', '2', '5', '0', '0', '2', '0', '8', '9', '1', '"', ',']

theorem object_fragment141801_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment141801Field006Chars00 ++ tail)) fragment141801Acc00600 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment141801Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_006"
  err.flush

noncomputable def fragment141801Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment141801Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '9', '2', '3', '6', '9', '1', '1', '7', '1', '5', '0', '3', '5', '9', '1', '9', '5', '1', '0', '4', '5', '4', '6', '1', '3', '2', '1', '6', '4', '9', '4', '7', '2', '1', '3', '2', '5', '3', '1', '0', '4', '1', '4', '7', '3', '8', '0', '8', '0', '8', '8', '9', '3', '4', '4', '1', '6', '5', '0', '7', '7', '1', '1', '4', '3', '3', '5', '2', '4', '8', '2', '4', '0', '6', '9', '7', '4', '0', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '8', '3', '9', '4', '5', '2', '3', '6', '7', '4', '6', '2', '1', '5', '8', '4', '8', '2', '8', '5', '9', '3', '9', '8', '0', '4', '6', '5', '9', '4', '3', '3', '5', '6', '1', '1', '5', '2', '2', '3', '4', '1', '4', '4', '7', '1', '0', '7', '3', '9', '1', '7', '7', '3', '4', '4', '5', '9', '8', '3', '7', '2', '0', '2', '0', '8', '1', '6', '8', '8', '7', '8', '6', '9', '5', '8', '4', '0', '8', '4', '9', '8', '7', '1', '7', '7', '0', '2', '9', '5', '8', '2', '3', '2', '1', '2', '2', '9', '5', '3', '8', '1', '9', '5', '5', '2', '3', '3', '9', '7', '3', '2', '3', '8', '4', '5', '1', '9'])
noncomputable def fragment141801Acc00800 : List (String × SourceJson) := (fragment141801Field007Key00, fragment141801Field007Value00) :: fragment141801Acc00700
noncomputable def fragment141801Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '9', '2', '3', '6', '9', '1', '1', '7', '1', '5', '0', '3', '5', '9', '1', '9', '5', '1', '0', '4', '5', '4', '6', '1', '3', '2', '1', '6', '4', '9', '4', '7', '2', '1', '3', '2', '5', '3', '1', '0', '4', '1', '4', '7', '3', '8', '0', '8', '0', '8', '8', '9', '3', '4', '4', '1', '6', '5', '0', '7', '7', '1', '1', '4', '3', '3', '5', '2', '4', '8', '2', '4', '0', '6', '9', '7', '4', '0', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '8', '3', '9', '4', '5', '2', '3', '6', '7', '4', '6', '2', '1', '5', '8', '4', '8', '2', '8', '5', '9', '3', '9', '8', '0', '4', '6', '5', '9', '4', '3', '3', '5', '6', '1', '1', '5', '2', '2', '3', '4', '1', '4', '4', '7', '1', '0', '7', '3', '9', '1', '7', '7', '3', '4', '4', '5', '9', '8', '3', '7', '2', '0', '2', '0', '8', '1', '6', '8', '8', '7', '8', '6', '9', '5', '8', '4', '0', '8', '4', '9', '8', '7', '1', '7', '7', '0', '2', '9', '5', '8', '2', '3', '2', '1', '2', '2', '9', '5', '3', '8', '1', '9', '5', '5', '2', '3', '3', '9', '7', '3', '2', '3', '8', '4', '5', '1', '9', '"', ',']

theorem object_fragment141801_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment141801Field007Chars00 ++ tail)) fragment141801Acc00700 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment141801Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_007"
  err.flush

noncomputable def fragment141801Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment141801Field008Value00 : SourceJson := .str (String.ofList ['7', '2', '6', '0', '9', '1', '3', '9', '3', '7', '7', '6', '7', '7', '5', '0'])
noncomputable def fragment141801Acc00900 : List (String × SourceJson) := (fragment141801Field008Key00, fragment141801Field008Value00) :: fragment141801Acc00800
noncomputable def fragment141801Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '2', '6', '0', '9', '1', '3', '9', '3', '7', '7', '6', '7', '7', '5', '0', '"', ',']

theorem object_fragment141801_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment141801Field008Chars00 ++ tail)) fragment141801Acc00800 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment141801Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_008"
  err.flush

noncomputable def fragment141801Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment141801Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '4', '5', '0', '1', '5', '2', '1', '5', '4', '9', '2', '3', '0', '9', '2'])
noncomputable def fragment141801Acc01000 : List (String × SourceJson) := (fragment141801Field009Key00, fragment141801Field009Value00) :: fragment141801Acc00900
noncomputable def fragment141801Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '4', '5', '0', '1', '5', '2', '1', '5', '4', '9', '2', '3', '0', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment141801_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment141801Field009Chars00 ++ tail)) fragment141801Acc00900 =
      .ok (.obj (fragment141801Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_object_field_009"
  err.flush

noncomputable def fragment141801Chars00 : List Char := '{' :: (fragment141801Field000Chars00 ++ fragment141801Field001Chars00 ++ fragment141801Field002Chars00 ++ fragment141801Field003Chars00 ++ fragment141801Field004Chars00 ++ fragment141801Field005Chars00 ++ fragment141801Field006Chars00 ++ fragment141801Field007Chars00 ++ fragment141801Field008Chars00 ++ fragment141801Field009Chars00)
noncomputable def fragment141801Value00 : SourceJson := .obj (fragment141801Acc01000.reverse)

theorem value_fragment141801 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 240) (fragment141801Chars00 ++ tail) =
      .ok (fragment141801Value00, tail) := by
  have hinput : fragment141801Chars00 ++ tail = '{' :: (fragment141801Field000Chars00 ++ (fragment141801Field001Chars00 ++ (fragment141801Field002Chars00 ++ (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment141801Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 240) (fragment141801Chars00 ++ tail) =
        SourceJson.value (fuel + 240) ('{' :: (fragment141801Field000Chars00 ++ (fragment141801Field001Chars00 ++ (fragment141801Field002Chars00 ++ (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 240)) hinput
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment141801Field000Chars00 ++ (fragment141801Field001Chars00 ++ (fragment141801Field002Chars00 ++ (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))))))))) fragment141801Acc00000 := by rfl
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment141801Field001Chars00 ++ (fragment141801Field002Chars00 ++ (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))))))))) fragment141801Acc00100 := object_fragment141801_field_000 fuel (fragment141801Field001Chars00 ++ (fragment141801Field002Chars00 ++ (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment141801Field002Chars00 ++ (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))))))) fragment141801Acc00200 := object_fragment141801_field_001 fuel (fragment141801Field002Chars00 ++ (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))))))) fragment141801Acc00300 := object_fragment141801_field_002 fuel (fragment141801Field003Chars00 ++ (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))))) fragment141801Acc00400 := object_fragment141801_field_003 fuel (fragment141801Field004Chars00 ++ (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))))) fragment141801Acc00500 := object_fragment141801_field_004 fuel (fragment141801Field005Chars00 ++ (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))) fragment141801Acc00600 := object_fragment141801_field_005 fuel (fragment141801Field006Chars00 ++ (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))) fragment141801Acc00700 := object_fragment141801_field_006 fuel (fragment141801Field007Chars00 ++ (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))) fragment141801Acc00800 := object_fragment141801_field_007 fuel (fragment141801Field008Chars00 ++ (fragment141801Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment141801Field009Chars00 ++ (tail))) fragment141801Acc00900 := object_fragment141801_field_008 fuel (fragment141801Field009Chars00 ++ (tail))
    _ = .ok (fragment141801Value00, tail) := object_fragment141801_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment141801_value_complete"
  err.flush

#print axioms object_fragment141801_field_000
#print axioms object_fragment141801_field_001
#print axioms object_fragment141801_field_002
#print axioms object_fragment141801_field_003
#print axioms object_fragment141801_field_004
#print axioms object_fragment141801_field_005
#print axioms object_fragment141801_field_006
#print axioms object_fragment141801_field_007
#print axioms object_fragment141801_field_008
#print axioms object_fragment141801_field_009
#print axioms value_fragment141801

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
