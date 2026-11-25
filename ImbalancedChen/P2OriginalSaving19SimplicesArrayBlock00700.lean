import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00600
import ImbalancedChen.P2OriginalSaving19ValueFragment14856300
import ImbalancedChen.P2OriginalSaving19ValueFragment15022400
import ImbalancedChen.P2OriginalSaving19ValueFragment15188400
import ImbalancedChen.P2OriginalSaving19ValueFragment15380000

/-! Original simplices block 7/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_028_before_generic"
  err.flush

noncomputable def simplicesChunk028LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk028SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk028Chars00 : List Char := simplicesChunk028LeadChars00 ++ fragment148563Chars00 ++ simplicesChunk028SuffixChars00
noncomputable def simplicesChunk028Push00 (acc : List SourceJson) : List SourceJson := fragment148563Value00 :: acc

noncomputable def simplicesChunk028AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_028_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 445)
      (SourceJson.white (simplicesChunk028LeadChars00 ++ (fragment148563Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 444) (fragment148563Chars00 ++ rest)).bind
        (simplicesChunk028AfterValue00 (fuel + 444) acc) := by rfl

theorem array_simplices_chunk_028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 445) (SourceJson.white (simplicesChunk028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 444) (SourceJson.white tail) (simplicesChunk028Push00 acc) := by
  have hinput : simplicesChunk028Chars00 ++ tail = simplicesChunk028LeadChars00 ++ (fragment148563Chars00 ++ (simplicesChunk028SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk028Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 445) (SourceJson.white (simplicesChunk028Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 445)
          (SourceJson.white (simplicesChunk028LeadChars00 ++ (fragment148563Chars00 ++ (simplicesChunk028SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 445) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 444) (fragment148563Chars00 ++ (simplicesChunk028SuffixChars00 ++ tail))).bind
        (simplicesChunk028AfterValue00 (fuel + 444) acc) := array_simplices_chunk_028_head fuel (simplicesChunk028SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment148563Value00, simplicesChunk028SuffixChars00 ++ tail)).bind
        (simplicesChunk028AfterValue00 (fuel + 444) acc) :=
      congrArg (fun result => result.bind (simplicesChunk028AfterValue00 (fuel + 444) acc))
        (value_fragment148563 (fuel + 180) (simplicesChunk028SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 444) (SourceJson.white tail) (simplicesChunk028Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02900 : List SourceJson := simplicesChunk028Push00 simplicesArrayAcc02800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_028_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_029_before_generic"
  err.flush

noncomputable def simplicesChunk029LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk029SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk029Chars00 : List Char := simplicesChunk029LeadChars00 ++ fragment150224Chars00 ++ simplicesChunk029SuffixChars00
noncomputable def simplicesChunk029Push00 (acc : List SourceJson) : List SourceJson := fragment150224Value00 :: acc

noncomputable def simplicesChunk029AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_029_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 444)
      (SourceJson.white (simplicesChunk029LeadChars00 ++ (fragment150224Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 443) (fragment150224Chars00 ++ rest)).bind
        (simplicesChunk029AfterValue00 (fuel + 443) acc) := by rfl

theorem array_simplices_chunk_029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 444) (SourceJson.white (simplicesChunk029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 443) (SourceJson.white tail) (simplicesChunk029Push00 acc) := by
  have hinput : simplicesChunk029Chars00 ++ tail = simplicesChunk029LeadChars00 ++ (fragment150224Chars00 ++ (simplicesChunk029SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk029Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 444) (SourceJson.white (simplicesChunk029Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 444)
          (SourceJson.white (simplicesChunk029LeadChars00 ++ (fragment150224Chars00 ++ (simplicesChunk029SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 444) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 443) (fragment150224Chars00 ++ (simplicesChunk029SuffixChars00 ++ tail))).bind
        (simplicesChunk029AfterValue00 (fuel + 443) acc) := array_simplices_chunk_029_head fuel (simplicesChunk029SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment150224Value00, simplicesChunk029SuffixChars00 ++ tail)).bind
        (simplicesChunk029AfterValue00 (fuel + 443) acc) :=
      congrArg (fun result => result.bind (simplicesChunk029AfterValue00 (fuel + 443) acc))
        (value_fragment150224 (fuel + 179) (simplicesChunk029SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 443) (SourceJson.white tail) (simplicesChunk029Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03000 : List SourceJson := simplicesChunk029Push00 simplicesArrayAcc02900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_029_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_030_before_generic"
  err.flush

noncomputable def simplicesChunk030LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk030SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk030Chars00 : List Char := simplicesChunk030LeadChars00 ++ fragment151884Chars00 ++ simplicesChunk030SuffixChars00
noncomputable def simplicesChunk030Push00 (acc : List SourceJson) : List SourceJson := fragment151884Value00 :: acc

noncomputable def simplicesChunk030AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_030_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 443)
      (SourceJson.white (simplicesChunk030LeadChars00 ++ (fragment151884Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 442) (fragment151884Chars00 ++ rest)).bind
        (simplicesChunk030AfterValue00 (fuel + 442) acc) := by rfl

theorem array_simplices_chunk_030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 443) (SourceJson.white (simplicesChunk030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 442) (SourceJson.white tail) (simplicesChunk030Push00 acc) := by
  have hinput : simplicesChunk030Chars00 ++ tail = simplicesChunk030LeadChars00 ++ (fragment151884Chars00 ++ (simplicesChunk030SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk030Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 443) (SourceJson.white (simplicesChunk030Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 443)
          (SourceJson.white (simplicesChunk030LeadChars00 ++ (fragment151884Chars00 ++ (simplicesChunk030SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 443) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 442) (fragment151884Chars00 ++ (simplicesChunk030SuffixChars00 ++ tail))).bind
        (simplicesChunk030AfterValue00 (fuel + 442) acc) := array_simplices_chunk_030_head fuel (simplicesChunk030SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment151884Value00, simplicesChunk030SuffixChars00 ++ tail)).bind
        (simplicesChunk030AfterValue00 (fuel + 442) acc) :=
      congrArg (fun result => result.bind (simplicesChunk030AfterValue00 (fuel + 442) acc))
        (value_fragment151884 (fuel + 57) (simplicesChunk030SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 442) (SourceJson.white tail) (simplicesChunk030Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03100 : List SourceJson := simplicesChunk030Push00 simplicesArrayAcc03000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_030_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_031_before_generic"
  err.flush

noncomputable def simplicesChunk031LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk031SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk031Chars00 : List Char := simplicesChunk031LeadChars00 ++ fragment153800Chars00 ++ simplicesChunk031SuffixChars00
noncomputable def simplicesChunk031Push00 (acc : List SourceJson) : List SourceJson := fragment153800Value00 :: acc

noncomputable def simplicesChunk031AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_031_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 442)
      (SourceJson.white (simplicesChunk031LeadChars00 ++ (fragment153800Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 441) (fragment153800Chars00 ++ rest)).bind
        (simplicesChunk031AfterValue00 (fuel + 441) acc) := by rfl

theorem array_simplices_chunk_031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 442) (SourceJson.white (simplicesChunk031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white tail) (simplicesChunk031Push00 acc) := by
  have hinput : simplicesChunk031Chars00 ++ tail = simplicesChunk031LeadChars00 ++ (fragment153800Chars00 ++ (simplicesChunk031SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk031Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 442) (SourceJson.white (simplicesChunk031Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 442)
          (SourceJson.white (simplicesChunk031LeadChars00 ++ (fragment153800Chars00 ++ (simplicesChunk031SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 442) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 441) (fragment153800Chars00 ++ (simplicesChunk031SuffixChars00 ++ tail))).bind
        (simplicesChunk031AfterValue00 (fuel + 441) acc) := array_simplices_chunk_031_head fuel (simplicesChunk031SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment153800Value00, simplicesChunk031SuffixChars00 ++ tail)).bind
        (simplicesChunk031AfterValue00 (fuel + 441) acc) :=
      congrArg (fun result => result.bind (simplicesChunk031AfterValue00 (fuel + 441) acc))
        (value_fragment153800 (fuel + 202) (simplicesChunk031SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 441) (SourceJson.white tail) (simplicesChunk031Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03200 : List SourceJson := simplicesChunk031Push00 simplicesArrayAcc03100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_031_generic_complete"
  err.flush

noncomputable def simplicesBlock007Chars00 : List Char := simplicesChunk028Chars00 ++ simplicesChunk029Chars00 ++ simplicesChunk030Chars00 ++ simplicesChunk031Chars00
noncomputable def simplicesBlock007Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk031Push00 (simplicesChunk030Push00 (simplicesChunk029Push00 (simplicesChunk028Push00 (acc))))

theorem array_simplices_block_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 445)
      (SourceJson.white (simplicesBlock007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white tail) (simplicesBlock007Push00 acc) := by
  have hinput : simplicesBlock007Chars00 ++ tail = simplicesChunk028Chars00 ++ (simplicesChunk029Chars00 ++ (simplicesChunk030Chars00 ++ (simplicesChunk031Chars00 ++ (tail)))) := by
    simp only [simplicesBlock007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 445)
        (SourceJson.white (simplicesBlock007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 445) (SourceJson.white (simplicesChunk028Chars00 ++ (simplicesChunk029Chars00 ++ (simplicesChunk030Chars00 ++ (simplicesChunk031Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 445) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 444) (SourceJson.white (simplicesChunk029Chars00 ++ (simplicesChunk030Chars00 ++ (simplicesChunk031Chars00 ++ (tail))))) (simplicesChunk028Push00 (acc)) := array_simplices_chunk_028 fuel (simplicesChunk029Chars00 ++ (simplicesChunk030Chars00 ++ (simplicesChunk031Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 443) (SourceJson.white (simplicesChunk030Chars00 ++ (simplicesChunk031Chars00 ++ (tail)))) (simplicesChunk029Push00 (simplicesChunk028Push00 (acc))) := array_simplices_chunk_029 fuel (simplicesChunk030Chars00 ++ (simplicesChunk031Chars00 ++ (tail))) (simplicesChunk028Push00 (acc))
    _ = SourceJson.array (fuel + 442) (SourceJson.white (simplicesChunk031Chars00 ++ (tail))) (simplicesChunk030Push00 (simplicesChunk029Push00 (simplicesChunk028Push00 (acc)))) := array_simplices_chunk_030 fuel (simplicesChunk031Chars00 ++ (tail)) (simplicesChunk029Push00 (simplicesChunk028Push00 (acc)))
    _ = SourceJson.array (fuel + 441) (SourceJson.white tail) (simplicesBlock007Push00 acc) := array_simplices_chunk_031 fuel (tail) (simplicesChunk030Push00 (simplicesChunk029Push00 (simplicesChunk028Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_007_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_007_prefix :
    (geometryChars00.drop 148557).take 6836 = simplicesBlock007Chars00 := by rfl

theorem geometryChars00_simplices_block_007_split :
    geometryChars00.drop 148557 = simplicesBlock007Chars00 ++ geometryChars00.drop 155393 := by
  calc
    geometryChars00.drop 148557 =
        (geometryChars00.drop 148557).take 6836 ++ (geometryChars00.drop 148557).drop 6836 :=
      (List.take_append_drop 6836 (geometryChars00.drop 148557)).symm
    _ = simplicesBlock007Chars00 ++ (geometryChars00.drop 148557).drop 6836 :=
      congrArg (fun p => p ++ (geometryChars00.drop 148557).drop 6836) geometryChars00_simplices_block_007_prefix
    _ = simplicesBlock007Chars00 ++ geometryChars00.drop 155393 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_007_after_single_binding"
  err.flush

theorem array_simplices_original_block_007 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 445)
      (SourceJson.white (geometryChars00.drop 148557)) acc =
      SourceJson.array (fuel + 441)
        (SourceJson.white (geometryChars00.drop 155393)) (simplicesBlock007Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 445) (SourceJson.white s) acc)
      geometryChars00_simplices_block_007_split).trans (array_simplices_block_007 fuel (geometryChars00.drop 155393) acc)

theorem simplices_array_through_block_007 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 441)
        (SourceJson.white (geometryChars00.drop 155393)) simplicesArrayAcc03200 := by
  exact (simplices_array_through_block_006 fuel).trans
    (array_simplices_original_block_007 fuel simplicesArrayAcc02800)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_007_complete"
  err.flush

#print axioms array_simplices_chunk_028_head
#print axioms array_simplices_chunk_028
#print axioms array_simplices_chunk_029_head
#print axioms array_simplices_chunk_029
#print axioms array_simplices_chunk_030_head
#print axioms array_simplices_chunk_030
#print axioms array_simplices_chunk_031_head
#print axioms array_simplices_chunk_031
#print axioms array_simplices_block_007
#print axioms geometryChars00_simplices_block_007_prefix
#print axioms geometryChars00_simplices_block_007_split
#print axioms array_simplices_original_block_007
#print axioms simplices_array_through_block_007

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
