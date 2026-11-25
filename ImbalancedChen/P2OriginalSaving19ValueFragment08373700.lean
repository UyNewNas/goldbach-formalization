import ImbalancedChen.P2OriginalSaving19ValueFragment08398300

/-! Self-delimiting original value fragment, raw candidate span [83737,84873). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment083737Acc00000 : List (String × SourceJson) := []

noncomputable def fragment083737Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment083737Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]
noncomputable def fragment083737Acc00100 : List (String × SourceJson) := (fragment083737Field000Key00, fragment083737Field000Value00) :: fragment083737Acc00000
noncomputable def fragment083737Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment083737_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment083737Field000Chars00 ++ tail)) fragment083737Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment083737Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment083737_object_field_000"
  err.flush

noncomputable def fragment083737Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment083737Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment083737Acc00200 : List (String × SourceJson) := (fragment083737Field001Key00, fragment083737Field001Value00) :: fragment083737Acc00100
noncomputable def fragment083737Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment083737_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment083737Field001Chars00 ++ tail)) fragment083737Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment083737Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment083737_object_field_001"
  err.flush

noncomputable def fragment083737Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment083737Field002Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment083737Acc00300 : List (String × SourceJson) := (fragment083737Field002Key00, fragment083737Field002Value00) :: fragment083737Acc00200
noncomputable def fragment083737Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '9', ',']

theorem object_fragment083737_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment083737Field002Chars00 ++ tail)) fragment083737Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment083737Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment083737_object_field_002"
  err.flush

noncomputable def fragment083737Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment083737Field003Value00 : SourceJson := fragment083983Value00
noncomputable def fragment083737Acc00400 : List (String × SourceJson) := (fragment083737Field003Key00, fragment083737Field003Value00) :: fragment083737Acc00300
noncomputable def fragment083737Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment083737Field003SuffixChars00 : List Char := [',']
noncomputable def fragment083737Field003Chars00 : List Char := fragment083737Field003HeaderChars00 ++ fragment083983Chars00 ++ fragment083737Field003SuffixChars00

noncomputable def fragment083737Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment083737Field003Key00, result.1) :: fragment083737Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment083737Field003Key00, result.1) :: fragment083737Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment083737_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment083737Field003HeaderChars00 ++ rest)) fragment083737Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment083737Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment083737_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment083737Field003Chars00 ++ tail)) fragment083737Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment083737Acc00400 := by
  have hinput : fragment083737Field003Chars00 ++ tail = fragment083737Field003HeaderChars00 ++ (fragment083983Chars00 ++ (fragment083737Field003SuffixChars00 ++ tail)) := by
    simp only [fragment083737Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment083737Field003Chars00 ++ tail)) fragment083737Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment083737Field003HeaderChars00 ++ (fragment083983Chars00 ++ (fragment083737Field003SuffixChars00 ++ tail)))) fragment083737Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment083737Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment083983Chars00 ++ (fragment083737Field003SuffixChars00 ++ tail))).bind
        (fragment083737Field003AfterValue00 (fuel + 17)) := object_fragment083737_field_003_header fuel (fragment083983Chars00 ++ (fragment083737Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment083983Value00, fragment083737Field003SuffixChars00 ++ tail)).bind (fragment083737Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment083737Field003AfterValue00 (fuel + 17)))
        (value_fragment083983 (fuel + 0) (fragment083737Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment083737Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment083737_object_field_003"
  err.flush

noncomputable def fragment083737Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment083737Field004Value00 : SourceJson := .number (String.ofList ['1', '2'])
noncomputable def fragment083737Acc00500 : List (String × SourceJson) := (fragment083737Field004Key00, fragment083737Field004Value00) :: fragment083737Acc00400
noncomputable def fragment083737Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment083737_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment083737Field004Chars00 ++ tail)) fragment083737Acc00400 =
      .ok (.obj (fragment083737Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment083737_object_field_004"
  err.flush

noncomputable def fragment083737Chars00 : List Char := '{' :: (fragment083737Field000Chars00 ++ fragment083737Field001Chars00 ++ fragment083737Field002Chars00 ++ fragment083737Field003Chars00 ++ fragment083737Field004Chars00)
noncomputable def fragment083737Value00 : SourceJson := .obj (fragment083737Acc00500.reverse)

theorem value_fragment083737 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment083737Chars00 ++ tail) =
      .ok (fragment083737Value00, tail) := by
  have hinput : fragment083737Chars00 ++ tail = '{' :: (fragment083737Field000Chars00 ++ (fragment083737Field001Chars00 ++ (fragment083737Field002Chars00 ++ (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail)))))) := by
    simp only [fragment083737Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment083737Chars00 ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment083737Field000Chars00 ++ (fragment083737Field001Chars00 ++ (fragment083737Field002Chars00 ++ (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment083737Field000Chars00 ++ (fragment083737Field001Chars00 ++ (fragment083737Field002Chars00 ++ (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail))))))) fragment083737Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment083737Field001Chars00 ++ (fragment083737Field002Chars00 ++ (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail)))))) fragment083737Acc00100 := object_fragment083737_field_000 fuel (fragment083737Field001Chars00 ++ (fragment083737Field002Chars00 ++ (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment083737Field002Chars00 ++ (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail))))) fragment083737Acc00200 := object_fragment083737_field_001 fuel (fragment083737Field002Chars00 ++ (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail)))) fragment083737Acc00300 := object_fragment083737_field_002 fuel (fragment083737Field003Chars00 ++ (fragment083737Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment083737Field004Chars00 ++ (tail))) fragment083737Acc00400 := object_fragment083737_field_003 fuel (fragment083737Field004Chars00 ++ (tail))
    _ = .ok (fragment083737Value00, tail) := object_fragment083737_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment083737_value_complete"
  err.flush

#print axioms object_fragment083737_field_000
#print axioms object_fragment083737_field_001
#print axioms object_fragment083737_field_002
#print axioms object_fragment083737_field_003_header
#print axioms object_fragment083737_field_003
#print axioms object_fragment083737_field_004
#print axioms value_fragment083737

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
