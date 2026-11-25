import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [189894,191356). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment189894Acc00000 : List (String × SourceJson) := []

noncomputable def fragment189894Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment189894Field000Value00 : SourceJson := .number (String.ofList ['5', '3'])
noncomputable def fragment189894Acc00100 : List (String × SourceJson) := (fragment189894Field000Key00, fragment189894Field000Value00) :: fragment189894Acc00000
noncomputable def fragment189894Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '3', ',']

theorem object_fragment189894_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 184) (SourceJson.white (fragment189894Field000Chars00 ++ tail)) fragment189894Acc00000 =
      SourceJson.object (fuel + 183) (SourceJson.white tail) fragment189894Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_000"
  err.flush

noncomputable def fragment189894Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment189894Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment189894Acc00200 : List (String × SourceJson) := (fragment189894Field001Key00, fragment189894Field001Value00) :: fragment189894Acc00100
noncomputable def fragment189894Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment189894_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 183) (SourceJson.white (fragment189894Field001Chars00 ++ tail)) fragment189894Acc00100 =
      SourceJson.object (fuel + 182) (SourceJson.white tail) fragment189894Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_001"
  err.flush

noncomputable def fragment189894Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment189894Field002Value00 : SourceJson := .str (String.ofList ['7', '6', '7', '2', '0', '2', '2', '3', '2', '3', '8', '9', '8', '8', '1', '0', '4', '7', '2', '2', '6', '8', '6', '1', '1', '1', '1', '/', '5', '8', '0', '7', '1', '7', '1', '5', '4', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment189894Acc00300 : List (String × SourceJson) := (fragment189894Field002Key00, fragment189894Field002Value00) :: fragment189894Acc00200
noncomputable def fragment189894Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '6', '7', '2', '0', '2', '2', '3', '2', '3', '8', '9', '8', '8', '1', '0', '4', '7', '2', '2', '6', '8', '6', '1', '1', '1', '1', '/', '5', '8', '0', '7', '1', '7', '1', '5', '4', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment189894_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 182) (SourceJson.white (fragment189894Field002Chars00 ++ tail)) fragment189894Acc00200 =
      SourceJson.object (fuel + 181) (SourceJson.white tail) fragment189894Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_002"
  err.flush

noncomputable def fragment189894Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment189894Field003Value00 : SourceJson := .str (String.ofList ['5', '4', '6', '7', '4', '3', '/', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment189894Acc00400 : List (String × SourceJson) := (fragment189894Field003Key00, fragment189894Field003Value00) :: fragment189894Acc00300
noncomputable def fragment189894Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '4', '6', '7', '4', '3', '/', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment189894_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 181) (SourceJson.white (fragment189894Field003Chars00 ++ tail)) fragment189894Acc00300 =
      SourceJson.object (fuel + 180) (SourceJson.white tail) fragment189894Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_003"
  err.flush

noncomputable def fragment189894Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment189894Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment189894Acc00500 : List (String × SourceJson) := (fragment189894Field004Key00, fragment189894Field004Value00) :: fragment189894Acc00400
noncomputable def fragment189894Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment189894_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 180) (SourceJson.white (fragment189894Field004Chars00 ++ tail)) fragment189894Acc00400 =
      SourceJson.object (fuel + 179) (SourceJson.white tail) fragment189894Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_004"
  err.flush

noncomputable def fragment189894Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment189894Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '5', '7', '8', '0', '3', '4', '5', '8', '1', '/', '9', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '4', '6', '9', '2', '4', '1', '9', '9', '/', '9', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '2', '0', '6', '3', '5', '5', '6', '1', '1', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '8', '4', '7', '1', '6', '4', '5', '7', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '5', '7', '2', '8', '1', '0', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '7', '2', '6', '6', '6', '5', '5', '7', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '2', '1', '5', '5', '9', '5', '7', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '4', '0', '0', '0', '7', '1', '/', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '2', '9', '3', '2', '2', '3', '9', '/', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '2', '9', '3', '0', '1', '1', '1', '/', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment189894Acc00600 : List (String × SourceJson) := (fragment189894Field005Key00, fragment189894Field005Value00) :: fragment189894Acc00500
noncomputable def fragment189894Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '7', '8', '0', '3', '4', '5', '8', '1', '/', '9', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '4', '6', '9', '2', '4', '1', '9', '9', '/', '9', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '0', '6', '3', '5', '5', '6', '1', '1', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '8', '4', '7', '1', '6', '4', '5', '7', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '7', '2', '8', '1', '0', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '7', '2', '6', '6', '6', '5', '5', '7', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '2', '1', '5', '5', '9', '5', '7', '/', '1', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '4', '0', '0', '0', '7', '1', '/', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '2', '9', '3', '2', '2', '3', '9', '/', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '2', '9', '3', '0', '1', '1', '1', '/', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment189894_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 179) (SourceJson.white (fragment189894Field005Chars00 ++ tail)) fragment189894Acc00500 =
      SourceJson.object (fuel + 178) (SourceJson.white tail) fragment189894Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_005"
  err.flush

noncomputable def fragment189894Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment189894Field006Value00 : SourceJson := .str (String.ofList ['3', '7', '3', '5', '0', '3', '9', '5', '5', '6', '0', '6', '0', '7', '4', '5', '3', '1', '3', '0', '9', '2', '6', '1', '4', '4', '5', '0', '4', '1', '1', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '6', '9', '9', '7', '8', '3', '7', '4', '3', '8', '7', '8', '9', '6', '6', '5', '3', '2', '9', '8', '9', '3', '0', '6', '9', '1', '8', '1', '6', '2', '8', '6', '5', '5', '9', '3', '0', '2', '7', '9', '0', '4', '2', '0', '1', '4', '9', '7', '4', '7', '1', '9', '4', '0', '2', '2', '4', '8', '5', '2', '3', '7', '7'])
noncomputable def fragment189894Acc00700 : List (String × SourceJson) := (fragment189894Field006Key00, fragment189894Field006Value00) :: fragment189894Acc00600
noncomputable def fragment189894Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '3', '5', '0', '3', '9', '5', '5', '6', '0', '6', '0', '7', '4', '5', '3', '1', '3', '0', '9', '2', '6', '1', '4', '4', '5', '0', '4', '1', '1', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '6', '9', '9', '7', '8', '3', '7', '4', '3', '8', '7', '8', '9', '6', '6', '5', '3', '2', '9', '8', '9', '3', '0', '6', '9', '1', '8', '1', '6', '2', '8', '6', '5', '5', '9', '3', '0', '2', '7', '9', '0', '4', '2', '0', '1', '4', '9', '7', '4', '7', '1', '9', '4', '0', '2', '2', '4', '8', '5', '2', '3', '7', '7', '"', ',']

theorem object_fragment189894_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 178) (SourceJson.white (fragment189894Field006Chars00 ++ tail)) fragment189894Acc00600 =
      SourceJson.object (fuel + 177) (SourceJson.white tail) fragment189894Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_006"
  err.flush

noncomputable def fragment189894Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment189894Field007Value00 : SourceJson := .str (String.ofList ['6', '6', '2', '4', '6', '6', '3', '6', '3', '1', '7', '2', '4', '3', '2', '0', '8', '7', '2', '9', '3', '0', '0', '4', '8', '4', '8', '0', '9', '9', '2', '9', '1', '9', '2', '4', '4', '8', '9', '1', '7', '0', '3', '4', '2', '7', '3', '0', '8', '4', '3', '2', '9', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '9', '1', '6', '0', '8', '0', '4', '0', '7', '8', '8', '0', '2', '8', '4', '5', '0', '6', '1', '5', '6', '5', '1', '7', '0', '2', '4', '1', '4', '9', '2', '2', '2', '2', '9', '0', '5', '2', '2', '7', '3', '0', '1', '2', '3', '7', '5', '8', '1', '7', '9', '0', '0', '0', '0', '8', '5', '2', '0', '9', '7', '8', '2', '0', '1', '5', '2', '6', '8', '8', '9', '5', '0', '2', '1', '0', '2', '6', '7', '5', '9', '0', '2', '6', '5', '2', '3', '9', '6', '2', '1', '9', '9'])
noncomputable def fragment189894Acc00800 : List (String × SourceJson) := (fragment189894Field007Key00, fragment189894Field007Value00) :: fragment189894Acc00700
noncomputable def fragment189894Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '6', '2', '4', '6', '6', '3', '6', '3', '1', '7', '2', '4', '3', '2', '0', '8', '7', '2', '9', '3', '0', '0', '4', '8', '4', '8', '0', '9', '9', '2', '9', '1', '9', '2', '4', '4', '8', '9', '1', '7', '0', '3', '4', '2', '7', '3', '0', '8', '4', '3', '2', '9', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '9', '1', '6', '0', '8', '0', '4', '0', '7', '8', '8', '0', '2', '8', '4', '5', '0', '6', '1', '5', '6', '5', '1', '7', '0', '2', '4', '1', '4', '9', '2', '2', '2', '2', '9', '0', '5', '2', '2', '7', '3', '0', '1', '2', '3', '7', '5', '8', '1', '7', '9', '0', '0', '0', '0', '8', '5', '2', '0', '9', '7', '8', '2', '0', '1', '5', '2', '6', '8', '8', '9', '5', '0', '2', '1', '0', '2', '6', '7', '5', '9', '0', '2', '6', '5', '2', '3', '9', '6', '2', '1', '9', '9', '"', ',']

theorem object_fragment189894_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 177) (SourceJson.white (fragment189894Field007Chars00 ++ tail)) fragment189894Acc00700 =
      SourceJson.object (fuel + 176) (SourceJson.white tail) fragment189894Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_007"
  err.flush

noncomputable def fragment189894Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment189894Field008Value00 : SourceJson := .str (String.ofList ['8', '7', '8', '1', '0', '7', '4', '7', '7', '4', '6', '5'])
noncomputable def fragment189894Acc00900 : List (String × SourceJson) := (fragment189894Field008Key00, fragment189894Field008Value00) :: fragment189894Acc00800
noncomputable def fragment189894Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '8', '1', '0', '7', '4', '7', '7', '4', '6', '5', '"', ',']

theorem object_fragment189894_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 176) (SourceJson.white (fragment189894Field008Chars00 ++ tail)) fragment189894Acc00800 =
      SourceJson.object (fuel + 175) (SourceJson.white tail) fragment189894Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_008"
  err.flush

noncomputable def fragment189894Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment189894Field009Value00 : SourceJson := .str (String.ofList ['2', '7', '7', '4', '6', '7', '5', '9', '1', '3', '2', '9', '3'])
noncomputable def fragment189894Acc01000 : List (String × SourceJson) := (fragment189894Field009Key00, fragment189894Field009Value00) :: fragment189894Acc00900
noncomputable def fragment189894Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '7', '4', '6', '7', '5', '9', '1', '3', '2', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment189894_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 175) (SourceJson.white (fragment189894Field009Chars00 ++ tail)) fragment189894Acc00900 =
      .ok (.obj (fragment189894Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_object_field_009"
  err.flush

noncomputable def fragment189894Chars00 : List Char := '{' :: (fragment189894Field000Chars00 ++ fragment189894Field001Chars00 ++ fragment189894Field002Chars00 ++ fragment189894Field003Chars00 ++ fragment189894Field004Chars00 ++ fragment189894Field005Chars00 ++ fragment189894Field006Chars00 ++ fragment189894Field007Chars00 ++ fragment189894Field008Chars00 ++ fragment189894Field009Chars00)
noncomputable def fragment189894Value00 : SourceJson := .obj (fragment189894Acc01000.reverse)

theorem value_fragment189894 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 185) (fragment189894Chars00 ++ tail) =
      .ok (fragment189894Value00, tail) := by
  have hinput : fragment189894Chars00 ++ tail = '{' :: (fragment189894Field000Chars00 ++ (fragment189894Field001Chars00 ++ (fragment189894Field002Chars00 ++ (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment189894Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 185) (fragment189894Chars00 ++ tail) =
        SourceJson.value (fuel + 185) ('{' :: (fragment189894Field000Chars00 ++ (fragment189894Field001Chars00 ++ (fragment189894Field002Chars00 ++ (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 185)) hinput
    _ = SourceJson.object (fuel + 184) (SourceJson.white (fragment189894Field000Chars00 ++ (fragment189894Field001Chars00 ++ (fragment189894Field002Chars00 ++ (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))))))))) fragment189894Acc00000 := by rfl
    _ = SourceJson.object (fuel + 183) (SourceJson.white (fragment189894Field001Chars00 ++ (fragment189894Field002Chars00 ++ (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))))))))) fragment189894Acc00100 := object_fragment189894_field_000 fuel (fragment189894Field001Chars00 ++ (fragment189894Field002Chars00 ++ (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 182) (SourceJson.white (fragment189894Field002Chars00 ++ (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))))))) fragment189894Acc00200 := object_fragment189894_field_001 fuel (fragment189894Field002Chars00 ++ (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 181) (SourceJson.white (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))))))) fragment189894Acc00300 := object_fragment189894_field_002 fuel (fragment189894Field003Chars00 ++ (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 180) (SourceJson.white (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))))) fragment189894Acc00400 := object_fragment189894_field_003 fuel (fragment189894Field004Chars00 ++ (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 179) (SourceJson.white (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))))) fragment189894Acc00500 := object_fragment189894_field_004 fuel (fragment189894Field005Chars00 ++ (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 178) (SourceJson.white (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))) fragment189894Acc00600 := object_fragment189894_field_005 fuel (fragment189894Field006Chars00 ++ (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 177) (SourceJson.white (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))) fragment189894Acc00700 := object_fragment189894_field_006 fuel (fragment189894Field007Chars00 ++ (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 176) (SourceJson.white (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))) fragment189894Acc00800 := object_fragment189894_field_007 fuel (fragment189894Field008Chars00 ++ (fragment189894Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 175) (SourceJson.white (fragment189894Field009Chars00 ++ (tail))) fragment189894Acc00900 := object_fragment189894_field_008 fuel (fragment189894Field009Chars00 ++ (tail))
    _ = .ok (fragment189894Value00, tail) := object_fragment189894_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment189894_value_complete"
  err.flush

#print axioms object_fragment189894_field_000
#print axioms object_fragment189894_field_001
#print axioms object_fragment189894_field_002
#print axioms object_fragment189894_field_003
#print axioms object_fragment189894_field_004
#print axioms object_fragment189894_field_005
#print axioms object_fragment189894_field_006
#print axioms object_fragment189894_field_007
#print axioms object_fragment189894_field_008
#print axioms object_fragment189894_field_009
#print axioms value_fragment189894

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
