import ImbalancedChen.P2OriginalSaving19ValueFragment08235400

/-! Self-delimiting original value fragment, raw candidate span [82058,83730). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment082058Acc00000 : List (String × SourceJson) := []

noncomputable def fragment082058Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment082058Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]
noncomputable def fragment082058Acc00100 : List (String × SourceJson) := (fragment082058Field000Key00, fragment082058Field000Value00) :: fragment082058Acc00000
noncomputable def fragment082058Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment082058_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment082058Field000Chars00 ++ tail)) fragment082058Acc00000 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment082058Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment082058_object_field_000"
  err.flush

noncomputable def fragment082058Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment082058Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment082058Acc00200 : List (String × SourceJson) := (fragment082058Field001Key00, fragment082058Field001Value00) :: fragment082058Acc00100
noncomputable def fragment082058Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment082058_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment082058Field001Chars00 ++ tail)) fragment082058Acc00100 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment082058Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment082058_object_field_001"
  err.flush

noncomputable def fragment082058Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment082058Field002Value00 : SourceJson := .number (String.ofList ['2', '1'])
noncomputable def fragment082058Acc00300 : List (String × SourceJson) := (fragment082058Field002Key00, fragment082058Field002Value00) :: fragment082058Acc00200
noncomputable def fragment082058Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '1', ',']

theorem object_fragment082058_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment082058Field002Chars00 ++ tail)) fragment082058Acc00200 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment082058Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment082058_object_field_002"
  err.flush

noncomputable def fragment082058Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment082058Field003Value00 : SourceJson := fragment082354Value00
noncomputable def fragment082058Acc00400 : List (String × SourceJson) := (fragment082058Field003Key00, fragment082058Field003Value00) :: fragment082058Acc00300
noncomputable def fragment082058Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment082058Field003SuffixChars00 : List Char := [',']
noncomputable def fragment082058Field003Chars00 : List Char := fragment082058Field003HeaderChars00 ++ fragment082354Chars00 ++ fragment082058Field003SuffixChars00

noncomputable def fragment082058Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment082058Field003Key00, result.1) :: fragment082058Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment082058Field003Key00, result.1) :: fragment082058Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment082058_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment082058Field003HeaderChars00 ++ rest)) fragment082058Acc00300 =
      (SourceJson.value (fuel + 22) rest).bind (fragment082058Field003AfterValue00 (fuel + 22)) := by rfl

theorem object_fragment082058_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment082058Field003Chars00 ++ tail)) fragment082058Acc00300 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment082058Acc00400 := by
  have hinput : fragment082058Field003Chars00 ++ tail = fragment082058Field003HeaderChars00 ++ (fragment082354Chars00 ++ (fragment082058Field003SuffixChars00 ++ tail)) := by
    simp only [fragment082058Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 23) (SourceJson.white (fragment082058Field003Chars00 ++ tail)) fragment082058Acc00300 =
        SourceJson.object (fuel + 23)
          (SourceJson.white (fragment082058Field003HeaderChars00 ++ (fragment082354Chars00 ++ (fragment082058Field003SuffixChars00 ++ tail)))) fragment082058Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 23) (SourceJson.white s) fragment082058Acc00300) hinput
    _ = (SourceJson.value (fuel + 22) (fragment082354Chars00 ++ (fragment082058Field003SuffixChars00 ++ tail))).bind
        (fragment082058Field003AfterValue00 (fuel + 22)) := object_fragment082058_field_003_header fuel (fragment082354Chars00 ++ (fragment082058Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment082354Value00, fragment082058Field003SuffixChars00 ++ tail)).bind (fragment082058Field003AfterValue00 (fuel + 22)) :=
      congrArg (fun result => result.bind (fragment082058Field003AfterValue00 (fuel + 22)))
        (value_fragment082354 (fuel + 0) (fragment082058Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 22) (SourceJson.white tail) fragment082058Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment082058_object_field_003"
  err.flush

noncomputable def fragment082058Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment082058Field004Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment082058Acc00500 : List (String × SourceJson) := (fragment082058Field004Key00, fragment082058Field004Value00) :: fragment082058Acc00400
noncomputable def fragment082058Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment082058_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment082058Field004Chars00 ++ tail)) fragment082058Acc00400 =
      .ok (.obj (fragment082058Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment082058_object_field_004"
  err.flush

noncomputable def fragment082058Chars00 : List Char := '{' :: (fragment082058Field000Chars00 ++ fragment082058Field001Chars00 ++ fragment082058Field002Chars00 ++ fragment082058Field003Chars00 ++ fragment082058Field004Chars00)
noncomputable def fragment082058Value00 : SourceJson := .obj (fragment082058Acc00500.reverse)

theorem value_fragment082058 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 27) (fragment082058Chars00 ++ tail) =
      .ok (fragment082058Value00, tail) := by
  have hinput : fragment082058Chars00 ++ tail = '{' :: (fragment082058Field000Chars00 ++ (fragment082058Field001Chars00 ++ (fragment082058Field002Chars00 ++ (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail)))))) := by
    simp only [fragment082058Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 27) (fragment082058Chars00 ++ tail) =
        SourceJson.value (fuel + 27) ('{' :: (fragment082058Field000Chars00 ++ (fragment082058Field001Chars00 ++ (fragment082058Field002Chars00 ++ (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 27)) hinput
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment082058Field000Chars00 ++ (fragment082058Field001Chars00 ++ (fragment082058Field002Chars00 ++ (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail))))))) fragment082058Acc00000 := by rfl
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment082058Field001Chars00 ++ (fragment082058Field002Chars00 ++ (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail)))))) fragment082058Acc00100 := object_fragment082058_field_000 fuel (fragment082058Field001Chars00 ++ (fragment082058Field002Chars00 ++ (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment082058Field002Chars00 ++ (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail))))) fragment082058Acc00200 := object_fragment082058_field_001 fuel (fragment082058Field002Chars00 ++ (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail)))) fragment082058Acc00300 := object_fragment082058_field_002 fuel (fragment082058Field003Chars00 ++ (fragment082058Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment082058Field004Chars00 ++ (tail))) fragment082058Acc00400 := object_fragment082058_field_003 fuel (fragment082058Field004Chars00 ++ (tail))
    _ = .ok (fragment082058Value00, tail) := object_fragment082058_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment082058_value_complete"
  err.flush

#print axioms object_fragment082058_field_000
#print axioms object_fragment082058_field_001
#print axioms object_fragment082058_field_002
#print axioms object_fragment082058_field_003_header
#print axioms object_fragment082058_field_003
#print axioms object_fragment082058_field_004
#print axioms value_fragment082058

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
