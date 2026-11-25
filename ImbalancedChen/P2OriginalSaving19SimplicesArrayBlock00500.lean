import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00400
import ImbalancedChen.P2OriginalSaving19ValueFragment13446200
import ImbalancedChen.P2OriginalSaving19ValueFragment13592500
import ImbalancedChen.P2OriginalSaving19ValueFragment13775100
import ImbalancedChen.P2OriginalSaving19ValueFragment13974300

/-! Original simplices block 5/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_020_before_generic"
  err.flush

noncomputable def simplicesChunk020LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk020SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk020Chars00 : List Char := simplicesChunk020LeadChars00 ++ fragment134462Chars00 ++ simplicesChunk020SuffixChars00
noncomputable def simplicesChunk020Push00 (acc : List SourceJson) : List SourceJson := fragment134462Value00 :: acc

noncomputable def simplicesChunk020AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_020_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 453)
      (SourceJson.white (simplicesChunk020LeadChars00 ++ (fragment134462Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 452) (fragment134462Chars00 ++ rest)).bind
        (simplicesChunk020AfterValue00 (fuel + 452) acc) := by rfl

theorem array_simplices_chunk_020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 453) (SourceJson.white (simplicesChunk020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 452) (SourceJson.white tail) (simplicesChunk020Push00 acc) := by
  have hinput : simplicesChunk020Chars00 ++ tail = simplicesChunk020LeadChars00 ++ (fragment134462Chars00 ++ (simplicesChunk020SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk020Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 453) (SourceJson.white (simplicesChunk020Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 453)
          (SourceJson.white (simplicesChunk020LeadChars00 ++ (fragment134462Chars00 ++ (simplicesChunk020SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 453) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 452) (fragment134462Chars00 ++ (simplicesChunk020SuffixChars00 ++ tail))).bind
        (simplicesChunk020AfterValue00 (fuel + 452) acc) := array_simplices_chunk_020_head fuel (simplicesChunk020SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment134462Value00, simplicesChunk020SuffixChars00 ++ tail)).bind
        (simplicesChunk020AfterValue00 (fuel + 452) acc) :=
      congrArg (fun result => result.bind (simplicesChunk020AfterValue00 (fuel + 452) acc))
        (value_fragment134462 (fuel + 286) (simplicesChunk020SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 452) (SourceJson.white tail) (simplicesChunk020Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02100 : List SourceJson := simplicesChunk020Push00 simplicesArrayAcc02000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_020_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_021_before_generic"
  err.flush

noncomputable def simplicesChunk021LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk021SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk021Chars00 : List Char := simplicesChunk021LeadChars00 ++ fragment135925Chars00 ++ simplicesChunk021SuffixChars00
noncomputable def simplicesChunk021Push00 (acc : List SourceJson) : List SourceJson := fragment135925Value00 :: acc

noncomputable def simplicesChunk021AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_021_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 452)
      (SourceJson.white (simplicesChunk021LeadChars00 ++ (fragment135925Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 451) (fragment135925Chars00 ++ rest)).bind
        (simplicesChunk021AfterValue00 (fuel + 451) acc) := by rfl

theorem array_simplices_chunk_021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 452) (SourceJson.white (simplicesChunk021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 451) (SourceJson.white tail) (simplicesChunk021Push00 acc) := by
  have hinput : simplicesChunk021Chars00 ++ tail = simplicesChunk021LeadChars00 ++ (fragment135925Chars00 ++ (simplicesChunk021SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk021Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 452) (SourceJson.white (simplicesChunk021Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 452)
          (SourceJson.white (simplicesChunk021LeadChars00 ++ (fragment135925Chars00 ++ (simplicesChunk021SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 452) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 451) (fragment135925Chars00 ++ (simplicesChunk021SuffixChars00 ++ tail))).bind
        (simplicesChunk021AfterValue00 (fuel + 451) acc) := array_simplices_chunk_021_head fuel (simplicesChunk021SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment135925Value00, simplicesChunk021SuffixChars00 ++ tail)).bind
        (simplicesChunk021AfterValue00 (fuel + 451) acc) :=
      congrArg (fun result => result.bind (simplicesChunk021AfterValue00 (fuel + 451) acc))
        (value_fragment135925 (fuel + 110) (simplicesChunk021SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 451) (SourceJson.white tail) (simplicesChunk021Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02200 : List SourceJson := simplicesChunk021Push00 simplicesArrayAcc02100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_021_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_022_before_generic"
  err.flush

noncomputable def simplicesChunk022LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk022SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk022Chars00 : List Char := simplicesChunk022LeadChars00 ++ fragment137751Chars00 ++ simplicesChunk022SuffixChars00
noncomputable def simplicesChunk022Push00 (acc : List SourceJson) : List SourceJson := fragment137751Value00 :: acc

noncomputable def simplicesChunk022AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_022_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 451)
      (SourceJson.white (simplicesChunk022LeadChars00 ++ (fragment137751Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 450) (fragment137751Chars00 ++ rest)).bind
        (simplicesChunk022AfterValue00 (fuel + 450) acc) := by rfl

theorem array_simplices_chunk_022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 451) (SourceJson.white (simplicesChunk022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 450) (SourceJson.white tail) (simplicesChunk022Push00 acc) := by
  have hinput : simplicesChunk022Chars00 ++ tail = simplicesChunk022LeadChars00 ++ (fragment137751Chars00 ++ (simplicesChunk022SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk022Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 451) (SourceJson.white (simplicesChunk022Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 451)
          (SourceJson.white (simplicesChunk022LeadChars00 ++ (fragment137751Chars00 ++ (simplicesChunk022SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 451) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 450) (fragment137751Chars00 ++ (simplicesChunk022SuffixChars00 ++ tail))).bind
        (simplicesChunk022AfterValue00 (fuel + 450) acc) := array_simplices_chunk_022_head fuel (simplicesChunk022SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment137751Value00, simplicesChunk022SuffixChars00 ++ tail)).bind
        (simplicesChunk022AfterValue00 (fuel + 450) acc) :=
      congrArg (fun result => result.bind (simplicesChunk022AfterValue00 (fuel + 450) acc))
        (value_fragment137751 (fuel + 25) (simplicesChunk022SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 450) (SourceJson.white tail) (simplicesChunk022Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02300 : List SourceJson := simplicesChunk022Push00 simplicesArrayAcc02200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_022_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_023_before_generic"
  err.flush

noncomputable def simplicesChunk023LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk023SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk023Chars00 : List Char := simplicesChunk023LeadChars00 ++ fragment139743Chars00 ++ simplicesChunk023SuffixChars00
noncomputable def simplicesChunk023Push00 (acc : List SourceJson) : List SourceJson := fragment139743Value00 :: acc

noncomputable def simplicesChunk023AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_023_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 450)
      (SourceJson.white (simplicesChunk023LeadChars00 ++ (fragment139743Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 449) (fragment139743Chars00 ++ rest)).bind
        (simplicesChunk023AfterValue00 (fuel + 449) acc) := by rfl

theorem array_simplices_chunk_023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 450) (SourceJson.white (simplicesChunk023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 449) (SourceJson.white tail) (simplicesChunk023Push00 acc) := by
  have hinput : simplicesChunk023Chars00 ++ tail = simplicesChunk023LeadChars00 ++ (fragment139743Chars00 ++ (simplicesChunk023SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk023Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 450) (SourceJson.white (simplicesChunk023Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 450)
          (SourceJson.white (simplicesChunk023LeadChars00 ++ (fragment139743Chars00 ++ (simplicesChunk023SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 450) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 449) (fragment139743Chars00 ++ (simplicesChunk023SuffixChars00 ++ tail))).bind
        (simplicesChunk023AfterValue00 (fuel + 449) acc) := array_simplices_chunk_023_head fuel (simplicesChunk023SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment139743Value00, simplicesChunk023SuffixChars00 ++ tail)).bind
        (simplicesChunk023AfterValue00 (fuel + 449) acc) :=
      congrArg (fun result => result.bind (simplicesChunk023AfterValue00 (fuel + 449) acc))
        (value_fragment139743 (fuel + 0) (simplicesChunk023SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 449) (SourceJson.white tail) (simplicesChunk023Push00 acc) := by rfl

noncomputable def simplicesArrayAcc02400 : List SourceJson := simplicesChunk023Push00 simplicesArrayAcc02300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_023_generic_complete"
  err.flush

noncomputable def simplicesBlock005Chars00 : List Char := simplicesChunk020Chars00 ++ simplicesChunk021Chars00 ++ simplicesChunk022Chars00 ++ simplicesChunk023Chars00
noncomputable def simplicesBlock005Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk023Push00 (simplicesChunk022Push00 (simplicesChunk021Push00 (simplicesChunk020Push00 (acc))))

theorem array_simplices_block_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 453)
      (SourceJson.white (simplicesBlock005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 449) (SourceJson.white tail) (simplicesBlock005Push00 acc) := by
  have hinput : simplicesBlock005Chars00 ++ tail = simplicesChunk020Chars00 ++ (simplicesChunk021Chars00 ++ (simplicesChunk022Chars00 ++ (simplicesChunk023Chars00 ++ (tail)))) := by
    simp only [simplicesBlock005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 453)
        (SourceJson.white (simplicesBlock005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 453) (SourceJson.white (simplicesChunk020Chars00 ++ (simplicesChunk021Chars00 ++ (simplicesChunk022Chars00 ++ (simplicesChunk023Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 453) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 452) (SourceJson.white (simplicesChunk021Chars00 ++ (simplicesChunk022Chars00 ++ (simplicesChunk023Chars00 ++ (tail))))) (simplicesChunk020Push00 (acc)) := array_simplices_chunk_020 fuel (simplicesChunk021Chars00 ++ (simplicesChunk022Chars00 ++ (simplicesChunk023Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 451) (SourceJson.white (simplicesChunk022Chars00 ++ (simplicesChunk023Chars00 ++ (tail)))) (simplicesChunk021Push00 (simplicesChunk020Push00 (acc))) := array_simplices_chunk_021 fuel (simplicesChunk022Chars00 ++ (simplicesChunk023Chars00 ++ (tail))) (simplicesChunk020Push00 (acc))
    _ = SourceJson.array (fuel + 450) (SourceJson.white (simplicesChunk023Chars00 ++ (tail))) (simplicesChunk022Push00 (simplicesChunk021Push00 (simplicesChunk020Push00 (acc)))) := array_simplices_chunk_022 fuel (simplicesChunk023Chars00 ++ (tail)) (simplicesChunk021Push00 (simplicesChunk020Push00 (acc)))
    _ = SourceJson.array (fuel + 449) (SourceJson.white tail) (simplicesBlock005Push00 acc) := array_simplices_chunk_023 fuel (tail) (simplicesChunk022Push00 (simplicesChunk021Push00 (simplicesChunk020Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_005_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_005_prefix :
    (geometryChars00.drop 134456).take 7339 = simplicesBlock005Chars00 := by rfl

theorem geometryChars00_simplices_block_005_split :
    geometryChars00.drop 134456 = simplicesBlock005Chars00 ++ geometryChars00.drop 141795 := by
  calc
    geometryChars00.drop 134456 =
        (geometryChars00.drop 134456).take 7339 ++ (geometryChars00.drop 134456).drop 7339 :=
      (List.take_append_drop 7339 (geometryChars00.drop 134456)).symm
    _ = simplicesBlock005Chars00 ++ (geometryChars00.drop 134456).drop 7339 :=
      congrArg (fun p => p ++ (geometryChars00.drop 134456).drop 7339) geometryChars00_simplices_block_005_prefix
    _ = simplicesBlock005Chars00 ++ geometryChars00.drop 141795 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_005_after_single_binding"
  err.flush

theorem array_simplices_original_block_005 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 453)
      (SourceJson.white (geometryChars00.drop 134456)) acc =
      SourceJson.array (fuel + 449)
        (SourceJson.white (geometryChars00.drop 141795)) (simplicesBlock005Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 453) (SourceJson.white s) acc)
      geometryChars00_simplices_block_005_split).trans (array_simplices_block_005 fuel (geometryChars00.drop 141795) acc)

theorem simplices_array_through_block_005 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 449)
        (SourceJson.white (geometryChars00.drop 141795)) simplicesArrayAcc02400 := by
  exact (simplices_array_through_block_004 fuel).trans
    (array_simplices_original_block_005 fuel simplicesArrayAcc02000)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_005_complete"
  err.flush

#print axioms array_simplices_chunk_020_head
#print axioms array_simplices_chunk_020
#print axioms array_simplices_chunk_021_head
#print axioms array_simplices_chunk_021
#print axioms array_simplices_chunk_022_head
#print axioms array_simplices_chunk_022
#print axioms array_simplices_chunk_023_head
#print axioms array_simplices_chunk_023
#print axioms array_simplices_block_005
#print axioms geometryChars00_simplices_block_005_prefix
#print axioms geometryChars00_simplices_block_005_split
#print axioms array_simplices_original_block_005
#print axioms simplices_array_through_block_005

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
