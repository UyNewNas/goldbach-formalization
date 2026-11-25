import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00000
import ImbalancedChen.P2OriginalSaving19ValueFragment06838000
import ImbalancedChen.P2OriginalSaving19ValueFragment06986400
import ImbalancedChen.P2OriginalSaving19ValueFragment07388300
import ImbalancedChen.P2OriginalSaving19ValueFragment07699800

/-! Original face_ledger block 1/8. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_004_before_generic"
  err.flush

noncomputable def faceLedgerChunk004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk004SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk004Chars00 : List Char := faceLedgerChunk004LeadChars00 ++ fragment068380Chars00 ++ faceLedgerChunk004SuffixChars00
noncomputable def faceLedgerChunk004Push00 (acc : List SourceJson) : List SourceJson := fragment068380Value00 :: acc

noncomputable def faceLedgerChunk004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (faceLedgerChunk004LeadChars00 ++ (fragment068380Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 49) (fragment068380Chars00 ++ rest)).bind
        (faceLedgerChunk004AfterValue00 (fuel + 49) acc) := by rfl

theorem array_faceLedger_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50) (SourceJson.white (faceLedgerChunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (faceLedgerChunk004Push00 acc) := by
  have hinput : faceLedgerChunk004Chars00 ++ tail = faceLedgerChunk004LeadChars00 ++ (fragment068380Chars00 ++ (faceLedgerChunk004SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 50) (SourceJson.white (faceLedgerChunk004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 50)
          (SourceJson.white (faceLedgerChunk004LeadChars00 ++ (fragment068380Chars00 ++ (faceLedgerChunk004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 50) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 49) (fragment068380Chars00 ++ (faceLedgerChunk004SuffixChars00 ++ tail))).bind
        (faceLedgerChunk004AfterValue00 (fuel + 49) acc) := array_faceLedger_chunk_004_head fuel (faceLedgerChunk004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment068380Value00, faceLedgerChunk004SuffixChars00 ++ tail)).bind
        (faceLedgerChunk004AfterValue00 (fuel + 49) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk004AfterValue00 (fuel + 49) acc))
        (value_fragment068380 (fuel + 23) (faceLedgerChunk004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 49) (SourceJson.white tail) (faceLedgerChunk004Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc00500 : List SourceJson := faceLedgerChunk004Push00 faceLedgerArrayAcc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_004_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_005_before_generic"
  err.flush

noncomputable def faceLedgerChunk005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk005SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk005Chars00 : List Char := faceLedgerChunk005LeadChars00 ++ fragment069864Chars00 ++ faceLedgerChunk005SuffixChars00
noncomputable def faceLedgerChunk005Push00 (acc : List SourceJson) : List SourceJson := fragment069864Value00 :: acc

noncomputable def faceLedgerChunk005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (faceLedgerChunk005LeadChars00 ++ (fragment069864Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 48) (fragment069864Chars00 ++ rest)).bind
        (faceLedgerChunk005AfterValue00 (fuel + 48) acc) := by rfl

theorem array_faceLedger_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49) (SourceJson.white (faceLedgerChunk005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail) (faceLedgerChunk005Push00 acc) := by
  have hinput : faceLedgerChunk005Chars00 ++ tail = faceLedgerChunk005LeadChars00 ++ (fragment069864Chars00 ++ (faceLedgerChunk005SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 49) (SourceJson.white (faceLedgerChunk005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 49)
          (SourceJson.white (faceLedgerChunk005LeadChars00 ++ (fragment069864Chars00 ++ (faceLedgerChunk005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 48) (fragment069864Chars00 ++ (faceLedgerChunk005SuffixChars00 ++ tail))).bind
        (faceLedgerChunk005AfterValue00 (fuel + 48) acc) := array_faceLedger_chunk_005_head fuel (faceLedgerChunk005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment069864Value00, faceLedgerChunk005SuffixChars00 ++ tail)).bind
        (faceLedgerChunk005AfterValue00 (fuel + 48) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk005AfterValue00 (fuel + 48) acc))
        (value_fragment069864 (fuel + 6) (faceLedgerChunk005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 48) (SourceJson.white tail) (faceLedgerChunk005Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc00600 : List SourceJson := faceLedgerChunk005Push00 faceLedgerArrayAcc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_005_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_006_before_generic"
  err.flush

noncomputable def faceLedgerChunk006LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk006SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk006Chars00 : List Char := faceLedgerChunk006LeadChars00 ++ fragment073883Chars00 ++ faceLedgerChunk006SuffixChars00
noncomputable def faceLedgerChunk006Push00 (acc : List SourceJson) : List SourceJson := fragment073883Value00 :: acc

noncomputable def faceLedgerChunk006AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_006_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (faceLedgerChunk006LeadChars00 ++ (fragment073883Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 47) (fragment073883Chars00 ++ rest)).bind
        (faceLedgerChunk006AfterValue00 (fuel + 47) acc) := by rfl

theorem array_faceLedger_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48) (SourceJson.white (faceLedgerChunk006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (faceLedgerChunk006Push00 acc) := by
  have hinput : faceLedgerChunk006Chars00 ++ tail = faceLedgerChunk006LeadChars00 ++ (fragment073883Chars00 ++ (faceLedgerChunk006SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 48) (SourceJson.white (faceLedgerChunk006Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 48)
          (SourceJson.white (faceLedgerChunk006LeadChars00 ++ (fragment073883Chars00 ++ (faceLedgerChunk006SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 48) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 47) (fragment073883Chars00 ++ (faceLedgerChunk006SuffixChars00 ++ tail))).bind
        (faceLedgerChunk006AfterValue00 (fuel + 47) acc) := array_faceLedger_chunk_006_head fuel (faceLedgerChunk006SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment073883Value00, faceLedgerChunk006SuffixChars00 ++ tail)).bind
        (faceLedgerChunk006AfterValue00 (fuel + 47) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk006AfterValue00 (fuel + 47) acc))
        (value_fragment073883 (fuel + 10) (faceLedgerChunk006SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 47) (SourceJson.white tail) (faceLedgerChunk006Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc00700 : List SourceJson := faceLedgerChunk006Push00 faceLedgerArrayAcc00600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_006_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_007_before_generic"
  err.flush

noncomputable def faceLedgerChunk007LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk007SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk007Chars00 : List Char := faceLedgerChunk007LeadChars00 ++ fragment076998Chars00 ++ faceLedgerChunk007SuffixChars00
noncomputable def faceLedgerChunk007Push00 (acc : List SourceJson) : List SourceJson := fragment076998Value00 :: acc

noncomputable def faceLedgerChunk007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47)
      (SourceJson.white (faceLedgerChunk007LeadChars00 ++ (fragment076998Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 46) (fragment076998Chars00 ++ rest)).bind
        (faceLedgerChunk007AfterValue00 (fuel + 46) acc) := by rfl

theorem array_faceLedger_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47) (SourceJson.white (faceLedgerChunk007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail) (faceLedgerChunk007Push00 acc) := by
  have hinput : faceLedgerChunk007Chars00 ++ tail = faceLedgerChunk007LeadChars00 ++ (fragment076998Chars00 ++ (faceLedgerChunk007SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 47) (SourceJson.white (faceLedgerChunk007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 47)
          (SourceJson.white (faceLedgerChunk007LeadChars00 ++ (fragment076998Chars00 ++ (faceLedgerChunk007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 47) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 46) (fragment076998Chars00 ++ (faceLedgerChunk007SuffixChars00 ++ tail))).bind
        (faceLedgerChunk007AfterValue00 (fuel + 46) acc) := array_faceLedger_chunk_007_head fuel (faceLedgerChunk007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment076998Value00, faceLedgerChunk007SuffixChars00 ++ tail)).bind
        (faceLedgerChunk007AfterValue00 (fuel + 46) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk007AfterValue00 (fuel + 46) acc))
        (value_fragment076998 (fuel + 17) (faceLedgerChunk007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 46) (SourceJson.white tail) (faceLedgerChunk007Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc00800 : List SourceJson := faceLedgerChunk007Push00 faceLedgerArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_007_generic_complete"
  err.flush

noncomputable def faceLedgerBlock001Chars00 : List Char := faceLedgerChunk004Chars00 ++ faceLedgerChunk005Chars00 ++ faceLedgerChunk006Chars00 ++ faceLedgerChunk007Chars00
noncomputable def faceLedgerBlock001Push00 (acc : List SourceJson) : List SourceJson := faceLedgerChunk007Push00 (faceLedgerChunk006Push00 (faceLedgerChunk005Push00 (faceLedgerChunk004Push00 (acc))))

theorem array_faceLedger_block_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (faceLedgerBlock001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail) (faceLedgerBlock001Push00 acc) := by
  have hinput : faceLedgerBlock001Chars00 ++ tail = faceLedgerChunk004Chars00 ++ (faceLedgerChunk005Chars00 ++ (faceLedgerChunk006Chars00 ++ (faceLedgerChunk007Chars00 ++ (tail)))) := by
    simp only [faceLedgerBlock001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 50)
        (SourceJson.white (faceLedgerBlock001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white (faceLedgerChunk004Chars00 ++ (faceLedgerChunk005Chars00 ++ (faceLedgerChunk006Chars00 ++ (faceLedgerChunk007Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 50) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 49) (SourceJson.white (faceLedgerChunk005Chars00 ++ (faceLedgerChunk006Chars00 ++ (faceLedgerChunk007Chars00 ++ (tail))))) (faceLedgerChunk004Push00 (acc)) := array_faceLedger_chunk_004 fuel (faceLedgerChunk005Chars00 ++ (faceLedgerChunk006Chars00 ++ (faceLedgerChunk007Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 48) (SourceJson.white (faceLedgerChunk006Chars00 ++ (faceLedgerChunk007Chars00 ++ (tail)))) (faceLedgerChunk005Push00 (faceLedgerChunk004Push00 (acc))) := array_faceLedger_chunk_005 fuel (faceLedgerChunk006Chars00 ++ (faceLedgerChunk007Chars00 ++ (tail))) (faceLedgerChunk004Push00 (acc))
    _ = SourceJson.array (fuel + 47) (SourceJson.white (faceLedgerChunk007Chars00 ++ (tail))) (faceLedgerChunk006Push00 (faceLedgerChunk005Push00 (faceLedgerChunk004Push00 (acc)))) := array_faceLedger_chunk_006 fuel (faceLedgerChunk007Chars00 ++ (tail)) (faceLedgerChunk005Push00 (faceLedgerChunk004Push00 (acc)))
    _ = SourceJson.array (fuel + 46) (SourceJson.white tail) (faceLedgerBlock001Push00 acc) := array_faceLedger_chunk_007 fuel (tail) (faceLedgerChunk006Push00 (faceLedgerChunk005Push00 (faceLedgerChunk004Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_001_before_single_binding"
  err.flush

theorem geometryChars00_faceLedger_block_001_prefix :
    (geometryChars00.drop 68374).take 10530 = faceLedgerBlock001Chars00 := by rfl

theorem geometryChars00_faceLedger_block_001_split :
    geometryChars00.drop 68374 = faceLedgerBlock001Chars00 ++ geometryChars00.drop 78904 := by
  calc
    geometryChars00.drop 68374 =
        (geometryChars00.drop 68374).take 10530 ++ (geometryChars00.drop 68374).drop 10530 :=
      (List.take_append_drop 10530 (geometryChars00.drop 68374)).symm
    _ = faceLedgerBlock001Chars00 ++ (geometryChars00.drop 68374).drop 10530 :=
      congrArg (fun p => p ++ (geometryChars00.drop 68374).drop 10530) geometryChars00_faceLedger_block_001_prefix
    _ = faceLedgerBlock001Chars00 ++ geometryChars00.drop 78904 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_001_after_single_binding"
  err.flush

theorem array_faceLedger_original_block_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (geometryChars00.drop 68374)) acc =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 78904)) (faceLedgerBlock001Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 50) (SourceJson.white s) acc)
      geometryChars00_faceLedger_block_001_split).trans (array_faceLedger_block_001 fuel (geometryChars00.drop 78904) acc)

theorem faceLedger_array_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) [] =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 78904)) faceLedgerArrayAcc00800 := by
  exact (faceLedger_array_through_block_000 fuel).trans
    (array_faceLedger_original_block_001 fuel faceLedgerArrayAcc00400)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_001_complete"
  err.flush

#print axioms array_faceLedger_chunk_004_head
#print axioms array_faceLedger_chunk_004
#print axioms array_faceLedger_chunk_005_head
#print axioms array_faceLedger_chunk_005
#print axioms array_faceLedger_chunk_006_head
#print axioms array_faceLedger_chunk_006
#print axioms array_faceLedger_chunk_007_head
#print axioms array_faceLedger_chunk_007
#print axioms array_faceLedger_block_001
#print axioms geometryChars00_faceLedger_block_001_prefix
#print axioms geometryChars00_faceLedger_block_001_split
#print axioms array_faceLedger_original_block_001
#print axioms faceLedger_array_through_block_001

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
