import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00200
import ImbalancedChen.P2OriginalSaving19ValueFragment12067600
import ImbalancedChen.P2OriginalSaving19ValueFragment12264300
import ImbalancedChen.P2OriginalSaving19ValueFragment12434400
import ImbalancedChen.P2OriginalSaving19ValueFragment12596200

/-! Original simplices block 3/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_012_before_generic"
  err.flush

noncomputable def simplicesChunk012LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk012SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk012Chars00 : List Char := simplicesChunk012LeadChars00 ++ fragment120676Chars00 ++ simplicesChunk012SuffixChars00
noncomputable def simplicesChunk012Push00 (acc : List SourceJson) : List SourceJson := fragment120676Value00 :: acc

noncomputable def simplicesChunk012AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_012_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 461)
      (SourceJson.white (simplicesChunk012LeadChars00 ++ (fragment120676Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 460) (fragment120676Chars00 ++ rest)).bind
        (simplicesChunk012AfterValue00 (fuel + 460) acc) := by rfl

theorem array_simplices_chunk_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 461) (SourceJson.white (simplicesChunk012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 460) (SourceJson.white tail) (simplicesChunk012Push00 acc) := by
  have hinput : simplicesChunk012Chars00 ++ tail = simplicesChunk012LeadChars00 ++ (fragment120676Chars00 ++ (simplicesChunk012SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk012Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 461) (SourceJson.white (simplicesChunk012Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 461)
          (SourceJson.white (simplicesChunk012LeadChars00 ++ (fragment120676Chars00 ++ (simplicesChunk012SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 461) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 460) (fragment120676Chars00 ++ (simplicesChunk012SuffixChars00 ++ tail))).bind
        (simplicesChunk012AfterValue00 (fuel + 460) acc) := array_simplices_chunk_012_head fuel (simplicesChunk012SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment120676Value00, simplicesChunk012SuffixChars00 ++ tail)).bind
        (simplicesChunk012AfterValue00 (fuel + 460) acc) :=
      congrArg (fun result => result.bind (simplicesChunk012AfterValue00 (fuel + 460) acc))
        (value_fragment120676 (fuel + 52) (simplicesChunk012SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 460) (SourceJson.white tail) (simplicesChunk012Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01300 : List SourceJson := simplicesChunk012Push00 simplicesArrayAcc01200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_012_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_013_before_generic"
  err.flush

noncomputable def simplicesChunk013LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk013SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk013Chars00 : List Char := simplicesChunk013LeadChars00 ++ fragment122643Chars00 ++ simplicesChunk013SuffixChars00
noncomputable def simplicesChunk013Push00 (acc : List SourceJson) : List SourceJson := fragment122643Value00 :: acc

noncomputable def simplicesChunk013AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_013_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 460)
      (SourceJson.white (simplicesChunk013LeadChars00 ++ (fragment122643Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 459) (fragment122643Chars00 ++ rest)).bind
        (simplicesChunk013AfterValue00 (fuel + 459) acc) := by rfl

theorem array_simplices_chunk_013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 460) (SourceJson.white (simplicesChunk013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 459) (SourceJson.white tail) (simplicesChunk013Push00 acc) := by
  have hinput : simplicesChunk013Chars00 ++ tail = simplicesChunk013LeadChars00 ++ (fragment122643Chars00 ++ (simplicesChunk013SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk013Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 460) (SourceJson.white (simplicesChunk013Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 460)
          (SourceJson.white (simplicesChunk013LeadChars00 ++ (fragment122643Chars00 ++ (simplicesChunk013SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 460) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 459) (fragment122643Chars00 ++ (simplicesChunk013SuffixChars00 ++ tail))).bind
        (simplicesChunk013AfterValue00 (fuel + 459) acc) := array_simplices_chunk_013_head fuel (simplicesChunk013SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment122643Value00, simplicesChunk013SuffixChars00 ++ tail)).bind
        (simplicesChunk013AfterValue00 (fuel + 459) acc) :=
      congrArg (fun result => result.bind (simplicesChunk013AfterValue00 (fuel + 459) acc))
        (value_fragment122643 (fuel + 185) (simplicesChunk013SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 459) (SourceJson.white tail) (simplicesChunk013Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01400 : List SourceJson := simplicesChunk013Push00 simplicesArrayAcc01300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_013_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_014_before_generic"
  err.flush

noncomputable def simplicesChunk014LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk014SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk014Chars00 : List Char := simplicesChunk014LeadChars00 ++ fragment124344Chars00 ++ simplicesChunk014SuffixChars00
noncomputable def simplicesChunk014Push00 (acc : List SourceJson) : List SourceJson := fragment124344Value00 :: acc

noncomputable def simplicesChunk014AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_014_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 459)
      (SourceJson.white (simplicesChunk014LeadChars00 ++ (fragment124344Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 458) (fragment124344Chars00 ++ rest)).bind
        (simplicesChunk014AfterValue00 (fuel + 458) acc) := by rfl

theorem array_simplices_chunk_014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 459) (SourceJson.white (simplicesChunk014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 458) (SourceJson.white tail) (simplicesChunk014Push00 acc) := by
  have hinput : simplicesChunk014Chars00 ++ tail = simplicesChunk014LeadChars00 ++ (fragment124344Chars00 ++ (simplicesChunk014SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk014Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 459) (SourceJson.white (simplicesChunk014Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 459)
          (SourceJson.white (simplicesChunk014LeadChars00 ++ (fragment124344Chars00 ++ (simplicesChunk014SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 459) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 458) (fragment124344Chars00 ++ (simplicesChunk014SuffixChars00 ++ tail))).bind
        (simplicesChunk014AfterValue00 (fuel + 458) acc) := array_simplices_chunk_014_head fuel (simplicesChunk014SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment124344Value00, simplicesChunk014SuffixChars00 ++ tail)).bind
        (simplicesChunk014AfterValue00 (fuel + 458) acc) :=
      congrArg (fun result => result.bind (simplicesChunk014AfterValue00 (fuel + 458) acc))
        (value_fragment124344 (fuel + 218) (simplicesChunk014SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 458) (SourceJson.white tail) (simplicesChunk014Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01500 : List SourceJson := simplicesChunk014Push00 simplicesArrayAcc01400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_014_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_015_before_generic"
  err.flush

noncomputable def simplicesChunk015LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk015SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk015Chars00 : List Char := simplicesChunk015LeadChars00 ++ fragment125962Chars00 ++ simplicesChunk015SuffixChars00
noncomputable def simplicesChunk015Push00 (acc : List SourceJson) : List SourceJson := fragment125962Value00 :: acc

noncomputable def simplicesChunk015AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_015_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 458)
      (SourceJson.white (simplicesChunk015LeadChars00 ++ (fragment125962Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 457) (fragment125962Chars00 ++ rest)).bind
        (simplicesChunk015AfterValue00 (fuel + 457) acc) := by rfl

theorem array_simplices_chunk_015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 458) (SourceJson.white (simplicesChunk015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 457) (SourceJson.white tail) (simplicesChunk015Push00 acc) := by
  have hinput : simplicesChunk015Chars00 ++ tail = simplicesChunk015LeadChars00 ++ (fragment125962Chars00 ++ (simplicesChunk015SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk015Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 458) (SourceJson.white (simplicesChunk015Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 458)
          (SourceJson.white (simplicesChunk015LeadChars00 ++ (fragment125962Chars00 ++ (simplicesChunk015SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 458) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 457) (fragment125962Chars00 ++ (simplicesChunk015SuffixChars00 ++ tail))).bind
        (simplicesChunk015AfterValue00 (fuel + 457) acc) := array_simplices_chunk_015_head fuel (simplicesChunk015SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment125962Value00, simplicesChunk015SuffixChars00 ++ tail)).bind
        (simplicesChunk015AfterValue00 (fuel + 457) acc) :=
      congrArg (fun result => result.bind (simplicesChunk015AfterValue00 (fuel + 457) acc))
        (value_fragment125962 (fuel + 238) (simplicesChunk015SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 457) (SourceJson.white tail) (simplicesChunk015Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01600 : List SourceJson := simplicesChunk015Push00 simplicesArrayAcc01500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_015_generic_complete"
  err.flush

noncomputable def simplicesBlock003Chars00 : List Char := simplicesChunk012Chars00 ++ simplicesChunk013Chars00 ++ simplicesChunk014Chars00 ++ simplicesChunk015Chars00
noncomputable def simplicesBlock003Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk015Push00 (simplicesChunk014Push00 (simplicesChunk013Push00 (simplicesChunk012Push00 (acc))))

theorem array_simplices_block_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 461)
      (SourceJson.white (simplicesBlock003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 457) (SourceJson.white tail) (simplicesBlock003Push00 acc) := by
  have hinput : simplicesBlock003Chars00 ++ tail = simplicesChunk012Chars00 ++ (simplicesChunk013Chars00 ++ (simplicesChunk014Chars00 ++ (simplicesChunk015Chars00 ++ (tail)))) := by
    simp only [simplicesBlock003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 461)
        (SourceJson.white (simplicesBlock003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 461) (SourceJson.white (simplicesChunk012Chars00 ++ (simplicesChunk013Chars00 ++ (simplicesChunk014Chars00 ++ (simplicesChunk015Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 461) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 460) (SourceJson.white (simplicesChunk013Chars00 ++ (simplicesChunk014Chars00 ++ (simplicesChunk015Chars00 ++ (tail))))) (simplicesChunk012Push00 (acc)) := array_simplices_chunk_012 fuel (simplicesChunk013Chars00 ++ (simplicesChunk014Chars00 ++ (simplicesChunk015Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 459) (SourceJson.white (simplicesChunk014Chars00 ++ (simplicesChunk015Chars00 ++ (tail)))) (simplicesChunk013Push00 (simplicesChunk012Push00 (acc))) := array_simplices_chunk_013 fuel (simplicesChunk014Chars00 ++ (simplicesChunk015Chars00 ++ (tail))) (simplicesChunk012Push00 (acc))
    _ = SourceJson.array (fuel + 458) (SourceJson.white (simplicesChunk015Chars00 ++ (tail))) (simplicesChunk014Push00 (simplicesChunk013Push00 (simplicesChunk012Push00 (acc)))) := array_simplices_chunk_014 fuel (simplicesChunk015Chars00 ++ (tail)) (simplicesChunk013Push00 (simplicesChunk012Push00 (acc)))
    _ = SourceJson.array (fuel + 457) (SourceJson.white tail) (simplicesBlock003Push00 acc) := array_simplices_chunk_015 fuel (tail) (simplicesChunk014Push00 (simplicesChunk013Push00 (simplicesChunk012Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_003_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_003_prefix :
    (geometryChars00.drop 120670).take 6832 = simplicesBlock003Chars00 := by rfl

theorem geometryChars00_simplices_block_003_split :
    geometryChars00.drop 120670 = simplicesBlock003Chars00 ++ geometryChars00.drop 127502 := by
  calc
    geometryChars00.drop 120670 =
        (geometryChars00.drop 120670).take 6832 ++ (geometryChars00.drop 120670).drop 6832 :=
      (List.take_append_drop 6832 (geometryChars00.drop 120670)).symm
    _ = simplicesBlock003Chars00 ++ (geometryChars00.drop 120670).drop 6832 :=
      congrArg (fun p => p ++ (geometryChars00.drop 120670).drop 6832) geometryChars00_simplices_block_003_prefix
    _ = simplicesBlock003Chars00 ++ geometryChars00.drop 127502 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_003_after_single_binding"
  err.flush

theorem array_simplices_original_block_003 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 461)
      (SourceJson.white (geometryChars00.drop 120670)) acc =
      SourceJson.array (fuel + 457)
        (SourceJson.white (geometryChars00.drop 127502)) (simplicesBlock003Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 461) (SourceJson.white s) acc)
      geometryChars00_simplices_block_003_split).trans (array_simplices_block_003 fuel (geometryChars00.drop 127502) acc)

theorem simplices_array_through_block_003 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 457)
        (SourceJson.white (geometryChars00.drop 127502)) simplicesArrayAcc01600 := by
  exact (simplices_array_through_block_002 fuel).trans
    (array_simplices_original_block_003 fuel simplicesArrayAcc01200)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_003_complete"
  err.flush

#print axioms array_simplices_chunk_012_head
#print axioms array_simplices_chunk_012
#print axioms array_simplices_chunk_013_head
#print axioms array_simplices_chunk_013
#print axioms array_simplices_chunk_014_head
#print axioms array_simplices_chunk_014
#print axioms array_simplices_chunk_015_head
#print axioms array_simplices_chunk_015
#print axioms array_simplices_block_003
#print axioms geometryChars00_simplices_block_003_prefix
#print axioms geometryChars00_simplices_block_003_split
#print axioms array_simplices_original_block_003
#print axioms simplices_array_through_block_003

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
