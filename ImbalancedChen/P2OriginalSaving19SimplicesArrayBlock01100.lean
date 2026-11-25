import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01000
import ImbalancedChen.P2OriginalSaving19ValueFragment17528600
import ImbalancedChen.P2OriginalSaving19ValueFragment17700200
import ImbalancedChen.P2OriginalSaving19ValueFragment17864700
import ImbalancedChen.P2OriginalSaving19ValueFragment18032000

/-! Original simplices block 11/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_044_before_generic"
  err.flush

noncomputable def simplicesChunk044LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk044SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk044Chars00 : List Char := simplicesChunk044LeadChars00 ++ fragment175286Chars00 ++ simplicesChunk044SuffixChars00
noncomputable def simplicesChunk044Push00 (acc : List SourceJson) : List SourceJson := fragment175286Value00 :: acc

noncomputable def simplicesChunk044AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_044_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 429)
      (SourceJson.white (simplicesChunk044LeadChars00 ++ (fragment175286Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 428) (fragment175286Chars00 ++ rest)).bind
        (simplicesChunk044AfterValue00 (fuel + 428) acc) := by rfl

theorem array_simplices_chunk_044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 429) (SourceJson.white (simplicesChunk044Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 428) (SourceJson.white tail) (simplicesChunk044Push00 acc) := by
  have hinput : simplicesChunk044Chars00 ++ tail = simplicesChunk044LeadChars00 ++ (fragment175286Chars00 ++ (simplicesChunk044SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk044Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 429) (SourceJson.white (simplicesChunk044Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 429)
          (SourceJson.white (simplicesChunk044LeadChars00 ++ (fragment175286Chars00 ++ (simplicesChunk044SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 429) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 428) (fragment175286Chars00 ++ (simplicesChunk044SuffixChars00 ++ tail))).bind
        (simplicesChunk044AfterValue00 (fuel + 428) acc) := array_simplices_chunk_044_head fuel (simplicesChunk044SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment175286Value00, simplicesChunk044SuffixChars00 ++ tail)).bind
        (simplicesChunk044AfterValue00 (fuel + 428) acc) :=
      congrArg (fun result => result.bind (simplicesChunk044AfterValue00 (fuel + 428) acc))
        (value_fragment175286 (fuel + 150) (simplicesChunk044SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 428) (SourceJson.white tail) (simplicesChunk044Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04500 : List SourceJson := simplicesChunk044Push00 simplicesArrayAcc04400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_044_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_045_before_generic"
  err.flush

noncomputable def simplicesChunk045LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk045SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk045Chars00 : List Char := simplicesChunk045LeadChars00 ++ fragment177002Chars00 ++ simplicesChunk045SuffixChars00
noncomputable def simplicesChunk045Push00 (acc : List SourceJson) : List SourceJson := fragment177002Value00 :: acc

noncomputable def simplicesChunk045AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_045_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 428)
      (SourceJson.white (simplicesChunk045LeadChars00 ++ (fragment177002Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 427) (fragment177002Chars00 ++ rest)).bind
        (simplicesChunk045AfterValue00 (fuel + 427) acc) := by rfl

theorem array_simplices_chunk_045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 428) (SourceJson.white (simplicesChunk045Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 427) (SourceJson.white tail) (simplicesChunk045Push00 acc) := by
  have hinput : simplicesChunk045Chars00 ++ tail = simplicesChunk045LeadChars00 ++ (fragment177002Chars00 ++ (simplicesChunk045SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk045Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 428) (SourceJson.white (simplicesChunk045Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 428)
          (SourceJson.white (simplicesChunk045LeadChars00 ++ (fragment177002Chars00 ++ (simplicesChunk045SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 428) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 427) (fragment177002Chars00 ++ (simplicesChunk045SuffixChars00 ++ tail))).bind
        (simplicesChunk045AfterValue00 (fuel + 427) acc) := array_simplices_chunk_045_head fuel (simplicesChunk045SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment177002Value00, simplicesChunk045SuffixChars00 ++ tail)).bind
        (simplicesChunk045AfterValue00 (fuel + 427) acc) :=
      congrArg (fun result => result.bind (simplicesChunk045AfterValue00 (fuel + 427) acc))
        (value_fragment177002 (fuel + 171) (simplicesChunk045SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 427) (SourceJson.white tail) (simplicesChunk045Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04600 : List SourceJson := simplicesChunk045Push00 simplicesArrayAcc04500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_045_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_046_before_generic"
  err.flush

noncomputable def simplicesChunk046LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk046SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk046Chars00 : List Char := simplicesChunk046LeadChars00 ++ fragment178647Chars00 ++ simplicesChunk046SuffixChars00
noncomputable def simplicesChunk046Push00 (acc : List SourceJson) : List SourceJson := fragment178647Value00 :: acc

noncomputable def simplicesChunk046AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_046_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 427)
      (SourceJson.white (simplicesChunk046LeadChars00 ++ (fragment178647Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 426) (fragment178647Chars00 ++ rest)).bind
        (simplicesChunk046AfterValue00 (fuel + 426) acc) := by rfl

theorem array_simplices_chunk_046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 427) (SourceJson.white (simplicesChunk046Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 426) (SourceJson.white tail) (simplicesChunk046Push00 acc) := by
  have hinput : simplicesChunk046Chars00 ++ tail = simplicesChunk046LeadChars00 ++ (fragment178647Chars00 ++ (simplicesChunk046SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk046Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 427) (SourceJson.white (simplicesChunk046Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 427)
          (SourceJson.white (simplicesChunk046LeadChars00 ++ (fragment178647Chars00 ++ (simplicesChunk046SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 427) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 426) (fragment178647Chars00 ++ (simplicesChunk046SuffixChars00 ++ tail))).bind
        (simplicesChunk046AfterValue00 (fuel + 426) acc) := array_simplices_chunk_046_head fuel (simplicesChunk046SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment178647Value00, simplicesChunk046SuffixChars00 ++ tail)).bind
        (simplicesChunk046AfterValue00 (fuel + 426) acc) :=
      congrArg (fun result => result.bind (simplicesChunk046AfterValue00 (fuel + 426) acc))
        (value_fragment178647 (fuel + 168) (simplicesChunk046SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 426) (SourceJson.white tail) (simplicesChunk046Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04700 : List SourceJson := simplicesChunk046Push00 simplicesArrayAcc04600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_046_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_047_before_generic"
  err.flush

noncomputable def simplicesChunk047LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk047SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk047Chars00 : List Char := simplicesChunk047LeadChars00 ++ fragment180320Chars00 ++ simplicesChunk047SuffixChars00
noncomputable def simplicesChunk047Push00 (acc : List SourceJson) : List SourceJson := fragment180320Value00 :: acc

noncomputable def simplicesChunk047AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_047_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 426)
      (SourceJson.white (simplicesChunk047LeadChars00 ++ (fragment180320Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 425) (fragment180320Chars00 ++ rest)).bind
        (simplicesChunk047AfterValue00 (fuel + 425) acc) := by rfl

theorem array_simplices_chunk_047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 426) (SourceJson.white (simplicesChunk047Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 425) (SourceJson.white tail) (simplicesChunk047Push00 acc) := by
  have hinput : simplicesChunk047Chars00 ++ tail = simplicesChunk047LeadChars00 ++ (fragment180320Chars00 ++ (simplicesChunk047SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk047Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 426) (SourceJson.white (simplicesChunk047Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 426)
          (SourceJson.white (simplicesChunk047LeadChars00 ++ (fragment180320Chars00 ++ (simplicesChunk047SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 426) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 425) (fragment180320Chars00 ++ (simplicesChunk047SuffixChars00 ++ tail))).bind
        (simplicesChunk047AfterValue00 (fuel + 425) acc) := array_simplices_chunk_047_head fuel (simplicesChunk047SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment180320Value00, simplicesChunk047SuffixChars00 ++ tail)).bind
        (simplicesChunk047AfterValue00 (fuel + 425) acc) :=
      congrArg (fun result => result.bind (simplicesChunk047AfterValue00 (fuel + 425) acc))
        (value_fragment180320 (fuel + 183) (simplicesChunk047SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 425) (SourceJson.white tail) (simplicesChunk047Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04800 : List SourceJson := simplicesChunk047Push00 simplicesArrayAcc04700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_047_generic_complete"
  err.flush

noncomputable def simplicesBlock011Chars00 : List Char := simplicesChunk044Chars00 ++ simplicesChunk045Chars00 ++ simplicesChunk046Chars00 ++ simplicesChunk047Chars00
noncomputable def simplicesBlock011Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk047Push00 (simplicesChunk046Push00 (simplicesChunk045Push00 (simplicesChunk044Push00 (acc))))

theorem array_simplices_block_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 429)
      (SourceJson.white (simplicesBlock011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 425) (SourceJson.white tail) (simplicesBlock011Push00 acc) := by
  have hinput : simplicesBlock011Chars00 ++ tail = simplicesChunk044Chars00 ++ (simplicesChunk045Chars00 ++ (simplicesChunk046Chars00 ++ (simplicesChunk047Chars00 ++ (tail)))) := by
    simp only [simplicesBlock011Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 429)
        (SourceJson.white (simplicesBlock011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 429) (SourceJson.white (simplicesChunk044Chars00 ++ (simplicesChunk045Chars00 ++ (simplicesChunk046Chars00 ++ (simplicesChunk047Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 429) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 428) (SourceJson.white (simplicesChunk045Chars00 ++ (simplicesChunk046Chars00 ++ (simplicesChunk047Chars00 ++ (tail))))) (simplicesChunk044Push00 (acc)) := array_simplices_chunk_044 fuel (simplicesChunk045Chars00 ++ (simplicesChunk046Chars00 ++ (simplicesChunk047Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 427) (SourceJson.white (simplicesChunk046Chars00 ++ (simplicesChunk047Chars00 ++ (tail)))) (simplicesChunk045Push00 (simplicesChunk044Push00 (acc))) := array_simplices_chunk_045 fuel (simplicesChunk046Chars00 ++ (simplicesChunk047Chars00 ++ (tail))) (simplicesChunk044Push00 (acc))
    _ = SourceJson.array (fuel + 426) (SourceJson.white (simplicesChunk047Chars00 ++ (tail))) (simplicesChunk046Push00 (simplicesChunk045Push00 (simplicesChunk044Push00 (acc)))) := array_simplices_chunk_046 fuel (simplicesChunk047Chars00 ++ (tail)) (simplicesChunk045Push00 (simplicesChunk044Push00 (acc)))
    _ = SourceJson.array (fuel + 425) (SourceJson.white tail) (simplicesBlock011Push00 acc) := array_simplices_chunk_047 fuel (tail) (simplicesChunk046Push00 (simplicesChunk045Push00 (simplicesChunk044Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_011_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_011_prefix :
    (geometryChars00.drop 175280).take 6641 = simplicesBlock011Chars00 := by rfl

theorem geometryChars00_simplices_block_011_split :
    geometryChars00.drop 175280 = simplicesBlock011Chars00 ++ geometryChars00.drop 181921 := by
  calc
    geometryChars00.drop 175280 =
        (geometryChars00.drop 175280).take 6641 ++ (geometryChars00.drop 175280).drop 6641 :=
      (List.take_append_drop 6641 (geometryChars00.drop 175280)).symm
    _ = simplicesBlock011Chars00 ++ (geometryChars00.drop 175280).drop 6641 :=
      congrArg (fun p => p ++ (geometryChars00.drop 175280).drop 6641) geometryChars00_simplices_block_011_prefix
    _ = simplicesBlock011Chars00 ++ geometryChars00.drop 181921 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_011_after_single_binding"
  err.flush

theorem array_simplices_original_block_011 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 429)
      (SourceJson.white (geometryChars00.drop 175280)) acc =
      SourceJson.array (fuel + 425)
        (SourceJson.white (geometryChars00.drop 181921)) (simplicesBlock011Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 429) (SourceJson.white s) acc)
      geometryChars00_simplices_block_011_split).trans (array_simplices_block_011 fuel (geometryChars00.drop 181921) acc)

theorem simplices_array_through_block_011 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 425)
        (SourceJson.white (geometryChars00.drop 181921)) simplicesArrayAcc04800 := by
  exact (simplices_array_through_block_010 fuel).trans
    (array_simplices_original_block_011 fuel simplicesArrayAcc04400)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_011_complete"
  err.flush

#print axioms array_simplices_chunk_044_head
#print axioms array_simplices_chunk_044
#print axioms array_simplices_chunk_045_head
#print axioms array_simplices_chunk_045
#print axioms array_simplices_chunk_046_head
#print axioms array_simplices_chunk_046
#print axioms array_simplices_chunk_047_head
#print axioms array_simplices_chunk_047
#print axioms array_simplices_block_011
#print axioms geometryChars00_simplices_block_011_prefix
#print axioms geometryChars00_simplices_block_011_split
#print axioms array_simplices_original_block_011
#print axioms simplices_array_through_block_011

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
