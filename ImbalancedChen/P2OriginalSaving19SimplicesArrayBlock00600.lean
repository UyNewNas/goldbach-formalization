import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00500
import ImbalancedChen.P2OriginalSaving19ValueFragment14180100
import ImbalancedChen.P2OriginalSaving19ValueFragment14342200
import ImbalancedChen.P2OriginalSaving19ValueFragment14503600
import ImbalancedChen.P2OriginalSaving19ValueFragment14690100

/-! Original simplices block 6/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_024_before_generic"
  err.flush

noncomputable def simplicesChunk024LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk024SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk024Chars00 : List Char := simplicesChunk024LeadChars00 ++ fragment141801Chars00 ++ simplicesChunk024SuffixChars00
noncomputable def simplicesChunk024Push00 (acc : List SourceJson) : List SourceJson := fragment141801Value00 :: acc

noncomputable def simplicesChunk024AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_024_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 449)
      (SourceJson.white (simplicesChunk024LeadChars00 ++ (fragment141801Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 448) (fragment141801Chars00 ++ rest)).bind
        (simplicesChunk024AfterValue00 (fuel + 448) acc) := by rfl

theorem array_simplices_chunk_024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 449) (SourceJson.white (simplicesChunk024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 448) (SourceJson.white tail) (simplicesChunk024Push00 acc) := by
  have hinput : simplicesChunk024Chars00 ++ tail = simplicesChunk024LeadChars00 ++ (fragment141801Chars00 ++ (simplicesChunk024SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk024Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 449) (SourceJson.white (simplicesChunk024Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 449)
          (SourceJson.white (simplicesChunk024LeadChars00 ++ (fragment141801Chars00 ++ (simplicesChunk024SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 449) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 448) (fragment141801Chars00 ++ (simplicesChunk024SuffixChars00 ++ tail))).bind
        (simplicesChunk024AfterValue00 (fuel + 448) acc) := array_simplices_chunk_024_head fuel (simplicesChunk024SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment141801Value00, simplicesChunk024SuffixChars00 ++ tail)).bind
        (simplicesChunk024AfterValue00 (fuel + 448) acc) :=
      congrArg (fun result => result.bind (simplicesChunk024AfterValue00 (fuel + 448) acc))
        (value_fragment141801 (fuel + 208) (simplicesChunk024SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 448) (SourceJson.white tail) (simplicesChunk024Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02500 : List SourceJson := simplicesChunk024Push00 simplicesArrayAcc02400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_024_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_025_before_generic"
  err.flush

noncomputable def simplicesChunk025LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk025SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk025Chars00 : List Char := simplicesChunk025LeadChars00 ++ fragment143422Chars00 ++ simplicesChunk025SuffixChars00
noncomputable def simplicesChunk025Push00 (acc : List SourceJson) : List SourceJson := fragment143422Value00 :: acc

noncomputable def simplicesChunk025AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_025_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 448)
      (SourceJson.white (simplicesChunk025LeadChars00 ++ (fragment143422Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 447) (fragment143422Chars00 ++ rest)).bind
        (simplicesChunk025AfterValue00 (fuel + 447) acc) := by rfl

theorem array_simplices_chunk_025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 448) (SourceJson.white (simplicesChunk025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 447) (SourceJson.white tail) (simplicesChunk025Push00 acc) := by
  have hinput : simplicesChunk025Chars00 ++ tail = simplicesChunk025LeadChars00 ++ (fragment143422Chars00 ++ (simplicesChunk025SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk025Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 448) (SourceJson.white (simplicesChunk025Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 448)
          (SourceJson.white (simplicesChunk025LeadChars00 ++ (fragment143422Chars00 ++ (simplicesChunk025SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 448) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 447) (fragment143422Chars00 ++ (simplicesChunk025SuffixChars00 ++ tail))).bind
        (simplicesChunk025AfterValue00 (fuel + 447) acc) := array_simplices_chunk_025_head fuel (simplicesChunk025SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment143422Value00, simplicesChunk025SuffixChars00 ++ tail)).bind
        (simplicesChunk025AfterValue00 (fuel + 447) acc) :=
      congrArg (fun result => result.bind (simplicesChunk025AfterValue00 (fuel + 447) acc))
        (value_fragment143422 (fuel + 210) (simplicesChunk025SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 447) (SourceJson.white tail) (simplicesChunk025Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02600 : List SourceJson := simplicesChunk025Push00 simplicesArrayAcc02500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_025_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_026_before_generic"
  err.flush

noncomputable def simplicesChunk026LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk026SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk026Chars00 : List Char := simplicesChunk026LeadChars00 ++ fragment145036Chars00 ++ simplicesChunk026SuffixChars00
noncomputable def simplicesChunk026Push00 (acc : List SourceJson) : List SourceJson := fragment145036Value00 :: acc

noncomputable def simplicesChunk026AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_026_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 447)
      (SourceJson.white (simplicesChunk026LeadChars00 ++ (fragment145036Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 446) (fragment145036Chars00 ++ rest)).bind
        (simplicesChunk026AfterValue00 (fuel + 446) acc) := by rfl

theorem array_simplices_chunk_026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 447) (SourceJson.white (simplicesChunk026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 446) (SourceJson.white tail) (simplicesChunk026Push00 acc) := by
  have hinput : simplicesChunk026Chars00 ++ tail = simplicesChunk026LeadChars00 ++ (fragment145036Chars00 ++ (simplicesChunk026SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk026Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 447) (SourceJson.white (simplicesChunk026Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 447)
          (SourceJson.white (simplicesChunk026LeadChars00 ++ (fragment145036Chars00 ++ (simplicesChunk026SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 447) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 446) (fragment145036Chars00 ++ (simplicesChunk026SuffixChars00 ++ tail))).bind
        (simplicesChunk026AfterValue00 (fuel + 446) acc) := array_simplices_chunk_026_head fuel (simplicesChunk026SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment145036Value00, simplicesChunk026SuffixChars00 ++ tail)).bind
        (simplicesChunk026AfterValue00 (fuel + 446) acc) :=
      congrArg (fun result => result.bind (simplicesChunk026AfterValue00 (fuel + 446) acc))
        (value_fragment145036 (fuel + 87) (simplicesChunk026SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 446) (SourceJson.white tail) (simplicesChunk026Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02700 : List SourceJson := simplicesChunk026Push00 simplicesArrayAcc02600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_026_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_027_before_generic"
  err.flush

noncomputable def simplicesChunk027LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk027SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk027Chars00 : List Char := simplicesChunk027LeadChars00 ++ fragment146901Chars00 ++ simplicesChunk027SuffixChars00
noncomputable def simplicesChunk027Push00 (acc : List SourceJson) : List SourceJson := fragment146901Value00 :: acc

noncomputable def simplicesChunk027AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_027_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 446)
      (SourceJson.white (simplicesChunk027LeadChars00 ++ (fragment146901Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 445) (fragment146901Chars00 ++ rest)).bind
        (simplicesChunk027AfterValue00 (fuel + 445) acc) := by rfl

theorem array_simplices_chunk_027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 446) (SourceJson.white (simplicesChunk027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 445) (SourceJson.white tail) (simplicesChunk027Push00 acc) := by
  have hinput : simplicesChunk027Chars00 ++ tail = simplicesChunk027LeadChars00 ++ (fragment146901Chars00 ++ (simplicesChunk027SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk027Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 446) (SourceJson.white (simplicesChunk027Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 446)
          (SourceJson.white (simplicesChunk027LeadChars00 ++ (fragment146901Chars00 ++ (simplicesChunk027SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 446) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 445) (fragment146901Chars00 ++ (simplicesChunk027SuffixChars00 ++ tail))).bind
        (simplicesChunk027AfterValue00 (fuel + 445) acc) := array_simplices_chunk_027_head fuel (simplicesChunk027SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment146901Value00, simplicesChunk027SuffixChars00 ++ tail)).bind
        (simplicesChunk027AfterValue00 (fuel + 445) acc) :=
      congrArg (fun result => result.bind (simplicesChunk027AfterValue00 (fuel + 445) acc))
        (value_fragment146901 (fuel + 178) (simplicesChunk027SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 445) (SourceJson.white tail) (simplicesChunk027Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02800 : List SourceJson := simplicesChunk027Push00 simplicesArrayAcc02700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_027_generic_complete"
  err.flush

noncomputable def simplicesBlock006Chars00 : List Char := simplicesChunk024Chars00 ++ simplicesChunk025Chars00 ++ simplicesChunk026Chars00 ++ simplicesChunk027Chars00
noncomputable def simplicesBlock006Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk027Push00 (simplicesChunk026Push00 (simplicesChunk025Push00 (simplicesChunk024Push00 (acc))))

theorem array_simplices_block_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 449)
      (SourceJson.white (simplicesBlock006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 445) (SourceJson.white tail) (simplicesBlock006Push00 acc) := by
  have hinput : simplicesBlock006Chars00 ++ tail = simplicesChunk024Chars00 ++ (simplicesChunk025Chars00 ++ (simplicesChunk026Chars00 ++ (simplicesChunk027Chars00 ++ (tail)))) := by
    simp only [simplicesBlock006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 449)
        (SourceJson.white (simplicesBlock006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 449) (SourceJson.white (simplicesChunk024Chars00 ++ (simplicesChunk025Chars00 ++ (simplicesChunk026Chars00 ++ (simplicesChunk027Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 449) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 448) (SourceJson.white (simplicesChunk025Chars00 ++ (simplicesChunk026Chars00 ++ (simplicesChunk027Chars00 ++ (tail))))) (simplicesChunk024Push00 (acc)) := array_simplices_chunk_024 fuel (simplicesChunk025Chars00 ++ (simplicesChunk026Chars00 ++ (simplicesChunk027Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 447) (SourceJson.white (simplicesChunk026Chars00 ++ (simplicesChunk027Chars00 ++ (tail)))) (simplicesChunk025Push00 (simplicesChunk024Push00 (acc))) := array_simplices_chunk_025 fuel (simplicesChunk026Chars00 ++ (simplicesChunk027Chars00 ++ (tail))) (simplicesChunk024Push00 (acc))
    _ = SourceJson.array (fuel + 446) (SourceJson.white (simplicesChunk027Chars00 ++ (tail))) (simplicesChunk026Push00 (simplicesChunk025Push00 (simplicesChunk024Push00 (acc)))) := array_simplices_chunk_026 fuel (simplicesChunk027Chars00 ++ (tail)) (simplicesChunk025Push00 (simplicesChunk024Push00 (acc)))
    _ = SourceJson.array (fuel + 445) (SourceJson.white tail) (simplicesBlock006Push00 acc) := array_simplices_chunk_027 fuel (tail) (simplicesChunk026Push00 (simplicesChunk025Push00 (simplicesChunk024Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_006_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_006_prefix :
    (geometryChars00.drop 141795).take 6762 = simplicesBlock006Chars00 := by rfl

theorem geometryChars00_simplices_block_006_split :
    geometryChars00.drop 141795 = simplicesBlock006Chars00 ++ geometryChars00.drop 148557 := by
  calc
    geometryChars00.drop 141795 =
        (geometryChars00.drop 141795).take 6762 ++ (geometryChars00.drop 141795).drop 6762 :=
      (List.take_append_drop 6762 (geometryChars00.drop 141795)).symm
    _ = simplicesBlock006Chars00 ++ (geometryChars00.drop 141795).drop 6762 :=
      congrArg (fun p => p ++ (geometryChars00.drop 141795).drop 6762) geometryChars00_simplices_block_006_prefix
    _ = simplicesBlock006Chars00 ++ geometryChars00.drop 148557 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_006_after_single_binding"
  err.flush

theorem array_simplices_original_block_006 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 449)
      (SourceJson.white (geometryChars00.drop 141795)) acc =
      SourceJson.array (fuel + 445)
        (SourceJson.white (geometryChars00.drop 148557)) (simplicesBlock006Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 449) (SourceJson.white s) acc)
      geometryChars00_simplices_block_006_split).trans (array_simplices_block_006 fuel (geometryChars00.drop 148557) acc)

theorem simplices_array_through_block_006 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 445)
        (SourceJson.white (geometryChars00.drop 148557)) simplicesArrayAcc02800 := by
  exact (simplices_array_through_block_005 fuel).trans
    (array_simplices_original_block_006 fuel simplicesArrayAcc02400)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_006_complete"
  err.flush

#print axioms array_simplices_chunk_024_head
#print axioms array_simplices_chunk_024
#print axioms array_simplices_chunk_025_head
#print axioms array_simplices_chunk_025
#print axioms array_simplices_chunk_026_head
#print axioms array_simplices_chunk_026
#print axioms array_simplices_chunk_027_head
#print axioms array_simplices_chunk_027
#print axioms array_simplices_block_006
#print axioms geometryChars00_simplices_block_006_prefix
#print axioms geometryChars00_simplices_block_006_split
#print axioms array_simplices_original_block_006
#print axioms simplices_array_through_block_006

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
