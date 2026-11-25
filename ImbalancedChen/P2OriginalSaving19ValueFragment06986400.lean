import ImbalancedChen.P2OriginalSaving19ValueFragment07031400

/-! Self-delimiting original value fragment, raw candidate span [69864,73876). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment069864Acc00000 : List (String × SourceJson) := []

noncomputable def fragment069864Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment069864Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]
noncomputable def fragment069864Acc00100 : List (String × SourceJson) := (fragment069864Field000Key00, fragment069864Field000Value00) :: fragment069864Acc00000
noncomputable def fragment069864Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment069864_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 41) (SourceJson.white (fragment069864Field000Chars00 ++ tail)) fragment069864Acc00000 =
      SourceJson.object (fuel + 40) (SourceJson.white tail) fragment069864Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment069864_object_field_000"
  err.flush

noncomputable def fragment069864Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment069864Field001Value00 : SourceJson := .number (String.ofList ['8'])
noncomputable def fragment069864Acc00200 : List (String × SourceJson) := (fragment069864Field001Key00, fragment069864Field001Value00) :: fragment069864Acc00100
noncomputable def fragment069864Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',']

theorem object_fragment069864_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 40) (SourceJson.white (fragment069864Field001Chars00 ++ tail)) fragment069864Acc00100 =
      SourceJson.object (fuel + 39) (SourceJson.white tail) fragment069864Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment069864_object_field_001"
  err.flush

noncomputable def fragment069864Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment069864Field002Value00 : SourceJson := .number (String.ofList ['2', '7'])
noncomputable def fragment069864Acc00300 : List (String × SourceJson) := (fragment069864Field002Key00, fragment069864Field002Value00) :: fragment069864Acc00200
noncomputable def fragment069864Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '7', ',']

theorem object_fragment069864_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 39) (SourceJson.white (fragment069864Field002Chars00 ++ tail)) fragment069864Acc00200 =
      SourceJson.object (fuel + 38) (SourceJson.white tail) fragment069864Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment069864_object_field_002"
  err.flush

noncomputable def fragment069864Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment069864Field003Value00 : SourceJson := fragment070314Value00
noncomputable def fragment069864Acc00400 : List (String × SourceJson) := (fragment069864Field003Key00, fragment069864Field003Value00) :: fragment069864Acc00300
noncomputable def fragment069864Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment069864Field003SuffixChars00 : List Char := [',']
noncomputable def fragment069864Field003Chars00 : List Char := fragment069864Field003HeaderChars00 ++ fragment070314Chars00 ++ fragment069864Field003SuffixChars00

noncomputable def fragment069864Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment069864Field003Key00, result.1) :: fragment069864Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment069864Field003Key00, result.1) :: fragment069864Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment069864_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 38) (SourceJson.white (fragment069864Field003HeaderChars00 ++ rest)) fragment069864Acc00300 =
      (SourceJson.value (fuel + 37) rest).bind (fragment069864Field003AfterValue00 (fuel + 37)) := by rfl

theorem object_fragment069864_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 38) (SourceJson.white (fragment069864Field003Chars00 ++ tail)) fragment069864Acc00300 =
      SourceJson.object (fuel + 37) (SourceJson.white tail) fragment069864Acc00400 := by
  have hinput : fragment069864Field003Chars00 ++ tail = fragment069864Field003HeaderChars00 ++ (fragment070314Chars00 ++ (fragment069864Field003SuffixChars00 ++ tail)) := by
    simp only [fragment069864Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 38) (SourceJson.white (fragment069864Field003Chars00 ++ tail)) fragment069864Acc00300 =
        SourceJson.object (fuel + 38)
          (SourceJson.white (fragment069864Field003HeaderChars00 ++ (fragment070314Chars00 ++ (fragment069864Field003SuffixChars00 ++ tail)))) fragment069864Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 38) (SourceJson.white s) fragment069864Acc00300) hinput
    _ = (SourceJson.value (fuel + 37) (fragment070314Chars00 ++ (fragment069864Field003SuffixChars00 ++ tail))).bind
        (fragment069864Field003AfterValue00 (fuel + 37)) := object_fragment069864_field_003_header fuel (fragment070314Chars00 ++ (fragment069864Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment070314Value00, fragment069864Field003SuffixChars00 ++ tail)).bind (fragment069864Field003AfterValue00 (fuel + 37)) :=
      congrArg (fun result => result.bind (fragment069864Field003AfterValue00 (fuel + 37)))
        (value_fragment070314 (fuel + 0) (fragment069864Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 37) (SourceJson.white tail) fragment069864Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment069864_object_field_003"
  err.flush

noncomputable def fragment069864Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment069864Field004Value00 : SourceJson := .number (String.ofList ['5', '6'])
noncomputable def fragment069864Acc00500 : List (String × SourceJson) := (fragment069864Field004Key00, fragment069864Field004Value00) :: fragment069864Acc00400
noncomputable def fragment069864Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment069864_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 37) (SourceJson.white (fragment069864Field004Chars00 ++ tail)) fragment069864Acc00400 =
      .ok (.obj (fragment069864Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment069864_object_field_004"
  err.flush

noncomputable def fragment069864Chars00 : List Char := '{' :: (fragment069864Field000Chars00 ++ fragment069864Field001Chars00 ++ fragment069864Field002Chars00 ++ fragment069864Field003Chars00 ++ fragment069864Field004Chars00)
noncomputable def fragment069864Value00 : SourceJson := .obj (fragment069864Acc00500.reverse)

theorem value_fragment069864 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 42) (fragment069864Chars00 ++ tail) =
      .ok (fragment069864Value00, tail) := by
  have hinput : fragment069864Chars00 ++ tail = '{' :: (fragment069864Field000Chars00 ++ (fragment069864Field001Chars00 ++ (fragment069864Field002Chars00 ++ (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail)))))) := by
    simp only [fragment069864Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 42) (fragment069864Chars00 ++ tail) =
        SourceJson.value (fuel + 42) ('{' :: (fragment069864Field000Chars00 ++ (fragment069864Field001Chars00 ++ (fragment069864Field002Chars00 ++ (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 42)) hinput
    _ = SourceJson.object (fuel + 41) (SourceJson.white (fragment069864Field000Chars00 ++ (fragment069864Field001Chars00 ++ (fragment069864Field002Chars00 ++ (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail))))))) fragment069864Acc00000 := by rfl
    _ = SourceJson.object (fuel + 40) (SourceJson.white (fragment069864Field001Chars00 ++ (fragment069864Field002Chars00 ++ (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail)))))) fragment069864Acc00100 := object_fragment069864_field_000 fuel (fragment069864Field001Chars00 ++ (fragment069864Field002Chars00 ++ (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 39) (SourceJson.white (fragment069864Field002Chars00 ++ (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail))))) fragment069864Acc00200 := object_fragment069864_field_001 fuel (fragment069864Field002Chars00 ++ (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 38) (SourceJson.white (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail)))) fragment069864Acc00300 := object_fragment069864_field_002 fuel (fragment069864Field003Chars00 ++ (fragment069864Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 37) (SourceJson.white (fragment069864Field004Chars00 ++ (tail))) fragment069864Acc00400 := object_fragment069864_field_003 fuel (fragment069864Field004Chars00 ++ (tail))
    _ = .ok (fragment069864Value00, tail) := object_fragment069864_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment069864_value_complete"
  err.flush

#print axioms object_fragment069864_field_000
#print axioms object_fragment069864_field_001
#print axioms object_fragment069864_field_002
#print axioms object_fragment069864_field_003_header
#print axioms object_fragment069864_field_003
#print axioms object_fragment069864_field_004
#print axioms value_fragment069864

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
