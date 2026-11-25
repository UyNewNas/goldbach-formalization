import ImbalancedChen.P2OriginalSaving19FaceLedgerField00
import ImbalancedChen.P2OriginalSaving19ValueFragment10044000
import ImbalancedChen.P2OriginalSaving19ValueFragment10206900
import ImbalancedChen.P2OriginalSaving19ValueFragment10402600
import ImbalancedChen.P2OriginalSaving19ValueFragment10573400

/-! Original simplices block 0/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def simplicesOpenChars00 : List Char := ['[']
noncomputable def simplicesArrayAcc00000 : List SourceJson := []

theorem geometryChars00_simplices_open_prefix :
    (geometryChars00.drop 100433).take 1 = simplicesOpenChars00 := by rfl

theorem geometryChars00_simplices_open_split :
    geometryChars00.drop 100433 = simplicesOpenChars00 ++ geometryChars00.drop 100434 := by
  calc
    geometryChars00.drop 100433 =
        (geometryChars00.drop 100433).take 1 ++ (geometryChars00.drop 100433).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 100433)).symm
    _ = simplicesOpenChars00 ++ (geometryChars00.drop 100433).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 100433).drop 1) geometryChars00_simplices_open_prefix
    _ = simplicesOpenChars00 ++ geometryChars00.drop 100434 := by rw [List.drop_drop]

theorem value_simplices_open (fuel : Nat) :
    SourceJson.value (fuel + 474) (geometryChars00.drop 100433) =
      SourceJson.array (fuel + 473)
        (SourceJson.white (geometryChars00.drop 100434)) [] := by
  calc
    SourceJson.value (fuel + 474) (geometryChars00.drop 100433) =
        SourceJson.value (fuel + 474)
          (simplicesOpenChars00 ++ geometryChars00.drop 100434) :=
      congrArg (SourceJson.value (fuel + 474)) geometryChars00_simplices_open_split
    _ = SourceJson.array (fuel + 473)
        (SourceJson.white (geometryChars00.drop 100434)) [] := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_000_before_generic"
  err.flush

noncomputable def simplicesChunk000LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk000SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk000Chars00 : List Char := simplicesChunk000LeadChars00 ++ fragment100440Chars00 ++ simplicesChunk000SuffixChars00
noncomputable def simplicesChunk000Push00 (acc : List SourceJson) : List SourceJson := fragment100440Value00 :: acc

noncomputable def simplicesChunk000AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_000_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (simplicesChunk000LeadChars00 ++ (fragment100440Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 472) (fragment100440Chars00 ++ rest)).bind
        (simplicesChunk000AfterValue00 (fuel + 472) acc) := by rfl

theorem array_simplices_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473) (SourceJson.white (simplicesChunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 472) (SourceJson.white tail) (simplicesChunk000Push00 acc) := by
  have hinput : simplicesChunk000Chars00 ++ tail = simplicesChunk000LeadChars00 ++ (fragment100440Chars00 ++ (simplicesChunk000SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk000Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 473) (SourceJson.white (simplicesChunk000Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 473)
          (SourceJson.white (simplicesChunk000LeadChars00 ++ (fragment100440Chars00 ++ (simplicesChunk000SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 473) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 472) (fragment100440Chars00 ++ (simplicesChunk000SuffixChars00 ++ tail))).bind
        (simplicesChunk000AfterValue00 (fuel + 472) acc) := array_simplices_chunk_000_head fuel (simplicesChunk000SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment100440Value00, simplicesChunk000SuffixChars00 ++ tail)).bind
        (simplicesChunk000AfterValue00 (fuel + 472) acc) :=
      congrArg (fun result => result.bind (simplicesChunk000AfterValue00 (fuel + 472) acc))
        (value_fragment100440 (fuel + 224) (simplicesChunk000SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 472) (SourceJson.white tail) (simplicesChunk000Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00100 : List SourceJson := simplicesChunk000Push00 simplicesArrayAcc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_000_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_001_before_generic"
  err.flush

noncomputable def simplicesChunk001LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk001SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk001Chars00 : List Char := simplicesChunk001LeadChars00 ++ fragment102069Chars00 ++ simplicesChunk001SuffixChars00
noncomputable def simplicesChunk001Push00 (acc : List SourceJson) : List SourceJson := fragment102069Value00 :: acc

noncomputable def simplicesChunk001AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_001_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 472)
      (SourceJson.white (simplicesChunk001LeadChars00 ++ (fragment102069Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 471) (fragment102069Chars00 ++ rest)).bind
        (simplicesChunk001AfterValue00 (fuel + 471) acc) := by rfl

theorem array_simplices_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 472) (SourceJson.white (simplicesChunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 471) (SourceJson.white tail) (simplicesChunk001Push00 acc) := by
  have hinput : simplicesChunk001Chars00 ++ tail = simplicesChunk001LeadChars00 ++ (fragment102069Chars00 ++ (simplicesChunk001SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 472) (SourceJson.white (simplicesChunk001Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 472)
          (SourceJson.white (simplicesChunk001LeadChars00 ++ (fragment102069Chars00 ++ (simplicesChunk001SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 472) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 471) (fragment102069Chars00 ++ (simplicesChunk001SuffixChars00 ++ tail))).bind
        (simplicesChunk001AfterValue00 (fuel + 471) acc) := array_simplices_chunk_001_head fuel (simplicesChunk001SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment102069Value00, simplicesChunk001SuffixChars00 ++ tail)).bind
        (simplicesChunk001AfterValue00 (fuel + 471) acc) :=
      congrArg (fun result => result.bind (simplicesChunk001AfterValue00 (fuel + 471) acc))
        (value_fragment102069 (fuel + 73) (simplicesChunk001SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 471) (SourceJson.white tail) (simplicesChunk001Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00200 : List SourceJson := simplicesChunk001Push00 simplicesArrayAcc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_001_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_002_before_generic"
  err.flush

noncomputable def simplicesChunk002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk002SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk002Chars00 : List Char := simplicesChunk002LeadChars00 ++ fragment104026Chars00 ++ simplicesChunk002SuffixChars00
noncomputable def simplicesChunk002Push00 (acc : List SourceJson) : List SourceJson := fragment104026Value00 :: acc

noncomputable def simplicesChunk002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 471)
      (SourceJson.white (simplicesChunk002LeadChars00 ++ (fragment104026Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 470) (fragment104026Chars00 ++ rest)).bind
        (simplicesChunk002AfterValue00 (fuel + 470) acc) := by rfl

theorem array_simplices_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 471) (SourceJson.white (simplicesChunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 470) (SourceJson.white tail) (simplicesChunk002Push00 acc) := by
  have hinput : simplicesChunk002Chars00 ++ tail = simplicesChunk002LeadChars00 ++ (fragment104026Chars00 ++ (simplicesChunk002SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 471) (SourceJson.white (simplicesChunk002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 471)
          (SourceJson.white (simplicesChunk002LeadChars00 ++ (fragment104026Chars00 ++ (simplicesChunk002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 471) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 470) (fragment104026Chars00 ++ (simplicesChunk002SuffixChars00 ++ tail))).bind
        (simplicesChunk002AfterValue00 (fuel + 470) acc) := array_simplices_chunk_002_head fuel (simplicesChunk002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment104026Value00, simplicesChunk002SuffixChars00 ++ tail)).bind
        (simplicesChunk002AfterValue00 (fuel + 470) acc) :=
      congrArg (fun result => result.bind (simplicesChunk002AfterValue00 (fuel + 470) acc))
        (value_fragment104026 (fuel + 194) (simplicesChunk002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 470) (SourceJson.white tail) (simplicesChunk002Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00300 : List SourceJson := simplicesChunk002Push00 simplicesArrayAcc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_002_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_003_before_generic"
  err.flush

noncomputable def simplicesChunk003LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk003SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk003Chars00 : List Char := simplicesChunk003LeadChars00 ++ fragment105734Chars00 ++ simplicesChunk003SuffixChars00
noncomputable def simplicesChunk003Push00 (acc : List SourceJson) : List SourceJson := fragment105734Value00 :: acc

noncomputable def simplicesChunk003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 470)
      (SourceJson.white (simplicesChunk003LeadChars00 ++ (fragment105734Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 469) (fragment105734Chars00 ++ rest)).bind
        (simplicesChunk003AfterValue00 (fuel + 469) acc) := by rfl

theorem array_simplices_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 470) (SourceJson.white (simplicesChunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 469) (SourceJson.white tail) (simplicesChunk003Push00 acc) := by
  have hinput : simplicesChunk003Chars00 ++ tail = simplicesChunk003LeadChars00 ++ (fragment105734Chars00 ++ (simplicesChunk003SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 470) (SourceJson.white (simplicesChunk003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 470)
          (SourceJson.white (simplicesChunk003LeadChars00 ++ (fragment105734Chars00 ++ (simplicesChunk003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 470) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 469) (fragment105734Chars00 ++ (simplicesChunk003SuffixChars00 ++ tail))).bind
        (simplicesChunk003AfterValue00 (fuel + 469) acc) := array_simplices_chunk_003_head fuel (simplicesChunk003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment105734Value00, simplicesChunk003SuffixChars00 ++ tail)).bind
        (simplicesChunk003AfterValue00 (fuel + 469) acc) :=
      congrArg (fun result => result.bind (simplicesChunk003AfterValue00 (fuel + 469) acc))
        (value_fragment105734 (fuel + 219) (simplicesChunk003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 469) (SourceJson.white tail) (simplicesChunk003Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00400 : List SourceJson := simplicesChunk003Push00 simplicesArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_003_generic_complete"
  err.flush

noncomputable def simplicesBlock000Chars00 : List Char := simplicesChunk000Chars00 ++ simplicesChunk001Chars00 ++ simplicesChunk002Chars00 ++ simplicesChunk003Chars00
noncomputable def simplicesBlock000Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk003Push00 (simplicesChunk002Push00 (simplicesChunk001Push00 (simplicesChunk000Push00 (acc))))

theorem array_simplices_block_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (simplicesBlock000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 469) (SourceJson.white tail) (simplicesBlock000Push00 acc) := by
  have hinput : simplicesBlock000Chars00 ++ tail = simplicesChunk000Chars00 ++ (simplicesChunk001Chars00 ++ (simplicesChunk002Chars00 ++ (simplicesChunk003Chars00 ++ (tail)))) := by
    simp only [simplicesBlock000Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 473)
        (SourceJson.white (simplicesBlock000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 473) (SourceJson.white (simplicesChunk000Chars00 ++ (simplicesChunk001Chars00 ++ (simplicesChunk002Chars00 ++ (simplicesChunk003Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 473) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 472) (SourceJson.white (simplicesChunk001Chars00 ++ (simplicesChunk002Chars00 ++ (simplicesChunk003Chars00 ++ (tail))))) (simplicesChunk000Push00 (acc)) := array_simplices_chunk_000 fuel (simplicesChunk001Chars00 ++ (simplicesChunk002Chars00 ++ (simplicesChunk003Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 471) (SourceJson.white (simplicesChunk002Chars00 ++ (simplicesChunk003Chars00 ++ (tail)))) (simplicesChunk001Push00 (simplicesChunk000Push00 (acc))) := array_simplices_chunk_001 fuel (simplicesChunk002Chars00 ++ (simplicesChunk003Chars00 ++ (tail))) (simplicesChunk000Push00 (acc))
    _ = SourceJson.array (fuel + 470) (SourceJson.white (simplicesChunk003Chars00 ++ (tail))) (simplicesChunk002Push00 (simplicesChunk001Push00 (simplicesChunk000Push00 (acc)))) := array_simplices_chunk_002 fuel (simplicesChunk003Chars00 ++ (tail)) (simplicesChunk001Push00 (simplicesChunk000Push00 (acc)))
    _ = SourceJson.array (fuel + 469) (SourceJson.white tail) (simplicesBlock000Push00 acc) := array_simplices_chunk_003 fuel (tail) (simplicesChunk002Push00 (simplicesChunk001Push00 (simplicesChunk000Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_000_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_000_prefix :
    (geometryChars00.drop 100434).take 6934 = simplicesBlock000Chars00 := by rfl

theorem geometryChars00_simplices_block_000_split :
    geometryChars00.drop 100434 = simplicesBlock000Chars00 ++ geometryChars00.drop 107368 := by
  calc
    geometryChars00.drop 100434 =
        (geometryChars00.drop 100434).take 6934 ++ (geometryChars00.drop 100434).drop 6934 :=
      (List.take_append_drop 6934 (geometryChars00.drop 100434)).symm
    _ = simplicesBlock000Chars00 ++ (geometryChars00.drop 100434).drop 6934 :=
      congrArg (fun p => p ++ (geometryChars00.drop 100434).drop 6934) geometryChars00_simplices_block_000_prefix
    _ = simplicesBlock000Chars00 ++ geometryChars00.drop 107368 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_000_after_single_binding"
  err.flush

theorem array_simplices_original_block_000 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) acc =
      SourceJson.array (fuel + 469)
        (SourceJson.white (geometryChars00.drop 107368)) (simplicesBlock000Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 473) (SourceJson.white s) acc)
      geometryChars00_simplices_block_000_split).trans (array_simplices_block_000 fuel (geometryChars00.drop 107368) acc)

theorem simplices_array_through_block_000 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 469)
        (SourceJson.white (geometryChars00.drop 107368)) simplicesArrayAcc00400 := by
  exact array_simplices_original_block_000 fuel simplicesArrayAcc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_000_complete"
  err.flush

#print axioms geometryChars00_simplices_open_prefix
#print axioms geometryChars00_simplices_open_split
#print axioms value_simplices_open
#print axioms array_simplices_chunk_000_head
#print axioms array_simplices_chunk_000
#print axioms array_simplices_chunk_001_head
#print axioms array_simplices_chunk_001
#print axioms array_simplices_chunk_002_head
#print axioms array_simplices_chunk_002
#print axioms array_simplices_chunk_003_head
#print axioms array_simplices_chunk_003
#print axioms array_simplices_block_000
#print axioms geometryChars00_simplices_block_000_prefix
#print axioms geometryChars00_simplices_block_000_split
#print axioms array_simplices_original_block_000
#print axioms simplices_array_through_block_000

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
