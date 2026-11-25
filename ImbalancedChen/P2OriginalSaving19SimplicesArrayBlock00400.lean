import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00300
import ImbalancedChen.P2OriginalSaving19ValueFragment12750800
import ImbalancedChen.P2OriginalSaving19ValueFragment12944100
import ImbalancedChen.P2OriginalSaving19ValueFragment13111500
import ImbalancedChen.P2OriginalSaving19ValueFragment13259700

/-! Original simplices block 4/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_016_before_generic"
  err.flush

noncomputable def simplicesChunk016LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk016SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk016Chars00 : List Char := simplicesChunk016LeadChars00 ++ fragment127508Chars00 ++ simplicesChunk016SuffixChars00
noncomputable def simplicesChunk016Push00 (acc : List SourceJson) : List SourceJson := fragment127508Value00 :: acc

noncomputable def simplicesChunk016AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_016_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 457)
      (SourceJson.white (simplicesChunk016LeadChars00 ++ (fragment127508Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 456) (fragment127508Chars00 ++ rest)).bind
        (simplicesChunk016AfterValue00 (fuel + 456) acc) := by rfl

theorem array_simplices_chunk_016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 457) (SourceJson.white (simplicesChunk016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 456) (SourceJson.white tail) (simplicesChunk016Push00 acc) := by
  have hinput : simplicesChunk016Chars00 ++ tail = simplicesChunk016LeadChars00 ++ (fragment127508Chars00 ++ (simplicesChunk016SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk016Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 457) (SourceJson.white (simplicesChunk016Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 457)
          (SourceJson.white (simplicesChunk016LeadChars00 ++ (fragment127508Chars00 ++ (simplicesChunk016SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 457) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 456) (fragment127508Chars00 ++ (simplicesChunk016SuffixChars00 ++ tail))).bind
        (simplicesChunk016AfterValue00 (fuel + 456) acc) := array_simplices_chunk_016_head fuel (simplicesChunk016SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment127508Value00, simplicesChunk016SuffixChars00 ++ tail)).bind
        (simplicesChunk016AfterValue00 (fuel + 456) acc) :=
      congrArg (fun result => result.bind (simplicesChunk016AfterValue00 (fuel + 456) acc))
        (value_fragment127508 (fuel + 58) (simplicesChunk016SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 456) (SourceJson.white tail) (simplicesChunk016Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01700 : List SourceJson := simplicesChunk016Push00 simplicesArrayAcc01600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_016_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_017_before_generic"
  err.flush

noncomputable def simplicesChunk017LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk017SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk017Chars00 : List Char := simplicesChunk017LeadChars00 ++ fragment129441Chars00 ++ simplicesChunk017SuffixChars00
noncomputable def simplicesChunk017Push00 (acc : List SourceJson) : List SourceJson := fragment129441Value00 :: acc

noncomputable def simplicesChunk017AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_017_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 456)
      (SourceJson.white (simplicesChunk017LeadChars00 ++ (fragment129441Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 455) (fragment129441Chars00 ++ rest)).bind
        (simplicesChunk017AfterValue00 (fuel + 455) acc) := by rfl

theorem array_simplices_chunk_017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 456) (SourceJson.white (simplicesChunk017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 455) (SourceJson.white tail) (simplicesChunk017Push00 acc) := by
  have hinput : simplicesChunk017Chars00 ++ tail = simplicesChunk017LeadChars00 ++ (fragment129441Chars00 ++ (simplicesChunk017SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk017Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 456) (SourceJson.white (simplicesChunk017Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 456)
          (SourceJson.white (simplicesChunk017LeadChars00 ++ (fragment129441Chars00 ++ (simplicesChunk017SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 456) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 455) (fragment129441Chars00 ++ (simplicesChunk017SuffixChars00 ++ tail))).bind
        (simplicesChunk017AfterValue00 (fuel + 455) acc) := array_simplices_chunk_017_head fuel (simplicesChunk017SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment129441Value00, simplicesChunk017SuffixChars00 ++ tail)).bind
        (simplicesChunk017AfterValue00 (fuel + 455) acc) :=
      congrArg (fun result => result.bind (simplicesChunk017AfterValue00 (fuel + 455) acc))
        (value_fragment129441 (fuel + 185) (simplicesChunk017SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 455) (SourceJson.white tail) (simplicesChunk017Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01800 : List SourceJson := simplicesChunk017Push00 simplicesArrayAcc01700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_017_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_018_before_generic"
  err.flush

noncomputable def simplicesChunk018LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk018SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk018Chars00 : List Char := simplicesChunk018LeadChars00 ++ fragment131115Chars00 ++ simplicesChunk018SuffixChars00
noncomputable def simplicesChunk018Push00 (acc : List SourceJson) : List SourceJson := fragment131115Value00 :: acc

noncomputable def simplicesChunk018AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_018_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 455)
      (SourceJson.white (simplicesChunk018LeadChars00 ++ (fragment131115Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 454) (fragment131115Chars00 ++ rest)).bind
        (simplicesChunk018AfterValue00 (fuel + 454) acc) := by rfl

theorem array_simplices_chunk_018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 455) (SourceJson.white (simplicesChunk018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 454) (SourceJson.white tail) (simplicesChunk018Push00 acc) := by
  have hinput : simplicesChunk018Chars00 ++ tail = simplicesChunk018LeadChars00 ++ (fragment131115Chars00 ++ (simplicesChunk018SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk018Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 455) (SourceJson.white (simplicesChunk018Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 455)
          (SourceJson.white (simplicesChunk018LeadChars00 ++ (fragment131115Chars00 ++ (simplicesChunk018SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 455) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 454) (fragment131115Chars00 ++ (simplicesChunk018SuffixChars00 ++ tail))).bind
        (simplicesChunk018AfterValue00 (fuel + 454) acc) := array_simplices_chunk_018_head fuel (simplicesChunk018SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment131115Value00, simplicesChunk018SuffixChars00 ++ tail)).bind
        (simplicesChunk018AfterValue00 (fuel + 454) acc) :=
      congrArg (fun result => result.bind (simplicesChunk018AfterValue00 (fuel + 454) acc))
        (value_fragment131115 (fuel + 266) (simplicesChunk018SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 454) (SourceJson.white tail) (simplicesChunk018Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01900 : List SourceJson := simplicesChunk018Push00 simplicesArrayAcc01800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_018_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_019_before_generic"
  err.flush

noncomputable def simplicesChunk019LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk019SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk019Chars00 : List Char := simplicesChunk019LeadChars00 ++ fragment132597Chars00 ++ simplicesChunk019SuffixChars00
noncomputable def simplicesChunk019Push00 (acc : List SourceJson) : List SourceJson := fragment132597Value00 :: acc

noncomputable def simplicesChunk019AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_019_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 454)
      (SourceJson.white (simplicesChunk019LeadChars00 ++ (fragment132597Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 453) (fragment132597Chars00 ++ rest)).bind
        (simplicesChunk019AfterValue00 (fuel + 453) acc) := by rfl

theorem array_simplices_chunk_019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 454) (SourceJson.white (simplicesChunk019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 453) (SourceJson.white tail) (simplicesChunk019Push00 acc) := by
  have hinput : simplicesChunk019Chars00 ++ tail = simplicesChunk019LeadChars00 ++ (fragment132597Chars00 ++ (simplicesChunk019SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk019Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 454) (SourceJson.white (simplicesChunk019Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 454)
          (SourceJson.white (simplicesChunk019LeadChars00 ++ (fragment132597Chars00 ++ (simplicesChunk019SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 454) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 453) (fragment132597Chars00 ++ (simplicesChunk019SuffixChars00 ++ tail))).bind
        (simplicesChunk019AfterValue00 (fuel + 453) acc) := array_simplices_chunk_019_head fuel (simplicesChunk019SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment132597Value00, simplicesChunk019SuffixChars00 ++ tail)).bind
        (simplicesChunk019AfterValue00 (fuel + 453) acc) :=
      congrArg (fun result => result.bind (simplicesChunk019AfterValue00 (fuel + 453) acc))
        (value_fragment132597 (fuel + 88) (simplicesChunk019SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 453) (SourceJson.white tail) (simplicesChunk019Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02000 : List SourceJson := simplicesChunk019Push00 simplicesArrayAcc01900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_019_generic_complete"
  err.flush

noncomputable def simplicesBlock004Chars00 : List Char := simplicesChunk016Chars00 ++ simplicesChunk017Chars00 ++ simplicesChunk018Chars00 ++ simplicesChunk019Chars00
noncomputable def simplicesBlock004Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk019Push00 (simplicesChunk018Push00 (simplicesChunk017Push00 (simplicesChunk016Push00 (acc))))

theorem array_simplices_block_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 457)
      (SourceJson.white (simplicesBlock004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 453) (SourceJson.white tail) (simplicesBlock004Push00 acc) := by
  have hinput : simplicesBlock004Chars00 ++ tail = simplicesChunk016Chars00 ++ (simplicesChunk017Chars00 ++ (simplicesChunk018Chars00 ++ (simplicesChunk019Chars00 ++ (tail)))) := by
    simp only [simplicesBlock004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 457)
        (SourceJson.white (simplicesBlock004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 457) (SourceJson.white (simplicesChunk016Chars00 ++ (simplicesChunk017Chars00 ++ (simplicesChunk018Chars00 ++ (simplicesChunk019Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 457) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 456) (SourceJson.white (simplicesChunk017Chars00 ++ (simplicesChunk018Chars00 ++ (simplicesChunk019Chars00 ++ (tail))))) (simplicesChunk016Push00 (acc)) := array_simplices_chunk_016 fuel (simplicesChunk017Chars00 ++ (simplicesChunk018Chars00 ++ (simplicesChunk019Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 455) (SourceJson.white (simplicesChunk018Chars00 ++ (simplicesChunk019Chars00 ++ (tail)))) (simplicesChunk017Push00 (simplicesChunk016Push00 (acc))) := array_simplices_chunk_017 fuel (simplicesChunk018Chars00 ++ (simplicesChunk019Chars00 ++ (tail))) (simplicesChunk016Push00 (acc))
    _ = SourceJson.array (fuel + 454) (SourceJson.white (simplicesChunk019Chars00 ++ (tail))) (simplicesChunk018Push00 (simplicesChunk017Push00 (simplicesChunk016Push00 (acc)))) := array_simplices_chunk_018 fuel (simplicesChunk019Chars00 ++ (tail)) (simplicesChunk017Push00 (simplicesChunk016Push00 (acc)))
    _ = SourceJson.array (fuel + 453) (SourceJson.white tail) (simplicesBlock004Push00 acc) := array_simplices_chunk_019 fuel (tail) (simplicesChunk018Push00 (simplicesChunk017Push00 (simplicesChunk016Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_004_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_004_prefix :
    (geometryChars00.drop 127502).take 6954 = simplicesBlock004Chars00 := by rfl

theorem geometryChars00_simplices_block_004_split :
    geometryChars00.drop 127502 = simplicesBlock004Chars00 ++ geometryChars00.drop 134456 := by
  calc
    geometryChars00.drop 127502 =
        (geometryChars00.drop 127502).take 6954 ++ (geometryChars00.drop 127502).drop 6954 :=
      (List.take_append_drop 6954 (geometryChars00.drop 127502)).symm
    _ = simplicesBlock004Chars00 ++ (geometryChars00.drop 127502).drop 6954 :=
      congrArg (fun p => p ++ (geometryChars00.drop 127502).drop 6954) geometryChars00_simplices_block_004_prefix
    _ = simplicesBlock004Chars00 ++ geometryChars00.drop 134456 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_004_after_single_binding"
  err.flush

theorem array_simplices_original_block_004 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 457)
      (SourceJson.white (geometryChars00.drop 127502)) acc =
      SourceJson.array (fuel + 453)
        (SourceJson.white (geometryChars00.drop 134456)) (simplicesBlock004Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 457) (SourceJson.white s) acc)
      geometryChars00_simplices_block_004_split).trans (array_simplices_block_004 fuel (geometryChars00.drop 134456) acc)

theorem simplices_array_through_block_004 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 453)
        (SourceJson.white (geometryChars00.drop 134456)) simplicesArrayAcc02000 := by
  exact (simplices_array_through_block_003 fuel).trans
    (array_simplices_original_block_004 fuel simplicesArrayAcc01600)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_004_complete"
  err.flush

#print axioms array_simplices_chunk_016_head
#print axioms array_simplices_chunk_016
#print axioms array_simplices_chunk_017_head
#print axioms array_simplices_chunk_017
#print axioms array_simplices_chunk_018_head
#print axioms array_simplices_chunk_018
#print axioms array_simplices_chunk_019_head
#print axioms array_simplices_chunk_019
#print axioms array_simplices_block_004
#print axioms geometryChars00_simplices_block_004_prefix
#print axioms geometryChars00_simplices_block_004_split
#print axioms array_simplices_original_block_004
#print axioms simplices_array_through_block_004

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
