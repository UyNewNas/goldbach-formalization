import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00100
import ImbalancedChen.P2OriginalSaving19ValueFragment07891000
import ImbalancedChen.P2OriginalSaving19ValueFragment08124100
import ImbalancedChen.P2OriginalSaving19ValueFragment08205800
import ImbalancedChen.P2OriginalSaving19ValueFragment08373700

/-! Original face_ledger block 2/8. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_008_before_generic"
  err.flush

noncomputable def faceLedgerChunk008LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk008SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk008Chars00 : List Char := faceLedgerChunk008LeadChars00 ++ fragment078910Chars00 ++ faceLedgerChunk008SuffixChars00
noncomputable def faceLedgerChunk008Push00 (acc : List SourceJson) : List SourceJson := fragment078910Value00 :: acc

noncomputable def faceLedgerChunk008AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_008_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (faceLedgerChunk008LeadChars00 ++ (fragment078910Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 45) (fragment078910Chars00 ++ rest)).bind
        (faceLedgerChunk008AfterValue00 (fuel + 45) acc) := by rfl

theorem array_faceLedger_chunk_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46) (SourceJson.white (faceLedgerChunk008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (faceLedgerChunk008Push00 acc) := by
  have hinput : faceLedgerChunk008Chars00 ++ tail = faceLedgerChunk008LeadChars00 ++ (fragment078910Chars00 ++ (faceLedgerChunk008SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 46) (SourceJson.white (faceLedgerChunk008Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 46)
          (SourceJson.white (faceLedgerChunk008LeadChars00 ++ (fragment078910Chars00 ++ (faceLedgerChunk008SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 46) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 45) (fragment078910Chars00 ++ (faceLedgerChunk008SuffixChars00 ++ tail))).bind
        (faceLedgerChunk008AfterValue00 (fuel + 45) acc) := array_faceLedger_chunk_008_head fuel (faceLedgerChunk008SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment078910Value00, faceLedgerChunk008SuffixChars00 ++ tail)).bind
        (faceLedgerChunk008AfterValue00 (fuel + 45) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk008AfterValue00 (fuel + 45) acc))
        (value_fragment078910 (fuel + 13) (faceLedgerChunk008SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 45) (SourceJson.white tail) (faceLedgerChunk008Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc00900 : List SourceJson := faceLedgerChunk008Push00 faceLedgerArrayAcc00800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_008_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_009_before_generic"
  err.flush

noncomputable def faceLedgerChunk009LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk009SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk009Chars00 : List Char := faceLedgerChunk009LeadChars00 ++ fragment081241Chars00 ++ faceLedgerChunk009SuffixChars00
noncomputable def faceLedgerChunk009Push00 (acc : List SourceJson) : List SourceJson := fragment081241Value00 :: acc

noncomputable def faceLedgerChunk009AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_009_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (faceLedgerChunk009LeadChars00 ++ (fragment081241Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 44) (fragment081241Chars00 ++ rest)).bind
        (faceLedgerChunk009AfterValue00 (fuel + 44) acc) := by rfl

theorem array_faceLedger_chunk_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45) (SourceJson.white (faceLedgerChunk009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 44) (SourceJson.white tail) (faceLedgerChunk009Push00 acc) := by
  have hinput : faceLedgerChunk009Chars00 ++ tail = faceLedgerChunk009LeadChars00 ++ (fragment081241Chars00 ++ (faceLedgerChunk009SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 45) (SourceJson.white (faceLedgerChunk009Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 45)
          (SourceJson.white (faceLedgerChunk009LeadChars00 ++ (fragment081241Chars00 ++ (faceLedgerChunk009SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 45) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 44) (fragment081241Chars00 ++ (faceLedgerChunk009SuffixChars00 ++ tail))).bind
        (faceLedgerChunk009AfterValue00 (fuel + 44) acc) := array_faceLedger_chunk_009_head fuel (faceLedgerChunk009SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment081241Value00, faceLedgerChunk009SuffixChars00 ++ tail)).bind
        (faceLedgerChunk009AfterValue00 (fuel + 44) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk009AfterValue00 (fuel + 44) acc))
        (value_fragment081241 (fuel + 24) (faceLedgerChunk009SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 44) (SourceJson.white tail) (faceLedgerChunk009Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc01000 : List SourceJson := faceLedgerChunk009Push00 faceLedgerArrayAcc00900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_009_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_010_before_generic"
  err.flush

noncomputable def faceLedgerChunk010LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk010SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk010Chars00 : List Char := faceLedgerChunk010LeadChars00 ++ fragment082058Chars00 ++ faceLedgerChunk010SuffixChars00
noncomputable def faceLedgerChunk010Push00 (acc : List SourceJson) : List SourceJson := fragment082058Value00 :: acc

noncomputable def faceLedgerChunk010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (faceLedgerChunk010LeadChars00 ++ (fragment082058Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 43) (fragment082058Chars00 ++ rest)).bind
        (faceLedgerChunk010AfterValue00 (fuel + 43) acc) := by rfl

theorem array_faceLedger_chunk_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44) (SourceJson.white (faceLedgerChunk010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail) (faceLedgerChunk010Push00 acc) := by
  have hinput : faceLedgerChunk010Chars00 ++ tail = faceLedgerChunk010LeadChars00 ++ (fragment082058Chars00 ++ (faceLedgerChunk010SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 44) (SourceJson.white (faceLedgerChunk010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 44)
          (SourceJson.white (faceLedgerChunk010LeadChars00 ++ (fragment082058Chars00 ++ (faceLedgerChunk010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 44) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 43) (fragment082058Chars00 ++ (faceLedgerChunk010SuffixChars00 ++ tail))).bind
        (faceLedgerChunk010AfterValue00 (fuel + 43) acc) := array_faceLedger_chunk_010_head fuel (faceLedgerChunk010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment082058Value00, faceLedgerChunk010SuffixChars00 ++ tail)).bind
        (faceLedgerChunk010AfterValue00 (fuel + 43) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk010AfterValue00 (fuel + 43) acc))
        (value_fragment082058 (fuel + 16) (faceLedgerChunk010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 43) (SourceJson.white tail) (faceLedgerChunk010Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc01100 : List SourceJson := faceLedgerChunk010Push00 faceLedgerArrayAcc01000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_010_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_011_before_generic"
  err.flush

noncomputable def faceLedgerChunk011LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk011SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk011Chars00 : List Char := faceLedgerChunk011LeadChars00 ++ fragment083737Chars00 ++ faceLedgerChunk011SuffixChars00
noncomputable def faceLedgerChunk011Push00 (acc : List SourceJson) : List SourceJson := fragment083737Value00 :: acc

noncomputable def faceLedgerChunk011AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_011_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43)
      (SourceJson.white (faceLedgerChunk011LeadChars00 ++ (fragment083737Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 42) (fragment083737Chars00 ++ rest)).bind
        (faceLedgerChunk011AfterValue00 (fuel + 42) acc) := by rfl

theorem array_faceLedger_chunk_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43) (SourceJson.white (faceLedgerChunk011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail) (faceLedgerChunk011Push00 acc) := by
  have hinput : faceLedgerChunk011Chars00 ++ tail = faceLedgerChunk011LeadChars00 ++ (fragment083737Chars00 ++ (faceLedgerChunk011SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk011Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 43) (SourceJson.white (faceLedgerChunk011Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 43)
          (SourceJson.white (faceLedgerChunk011LeadChars00 ++ (fragment083737Chars00 ++ (faceLedgerChunk011SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 43) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 42) (fragment083737Chars00 ++ (faceLedgerChunk011SuffixChars00 ++ tail))).bind
        (faceLedgerChunk011AfterValue00 (fuel + 42) acc) := array_faceLedger_chunk_011_head fuel (faceLedgerChunk011SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment083737Value00, faceLedgerChunk011SuffixChars00 ++ tail)).bind
        (faceLedgerChunk011AfterValue00 (fuel + 42) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk011AfterValue00 (fuel + 42) acc))
        (value_fragment083737 (fuel + 20) (faceLedgerChunk011SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 42) (SourceJson.white tail) (faceLedgerChunk011Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc01200 : List SourceJson := faceLedgerChunk011Push00 faceLedgerArrayAcc01100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_011_generic_complete"
  err.flush

noncomputable def faceLedgerBlock002Chars00 : List Char := faceLedgerChunk008Chars00 ++ faceLedgerChunk009Chars00 ++ faceLedgerChunk010Chars00 ++ faceLedgerChunk011Chars00
noncomputable def faceLedgerBlock002Push00 (acc : List SourceJson) : List SourceJson := faceLedgerChunk011Push00 (faceLedgerChunk010Push00 (faceLedgerChunk009Push00 (faceLedgerChunk008Push00 (acc))))

theorem array_faceLedger_block_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (faceLedgerBlock002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail) (faceLedgerBlock002Push00 acc) := by
  have hinput : faceLedgerBlock002Chars00 ++ tail = faceLedgerChunk008Chars00 ++ (faceLedgerChunk009Chars00 ++ (faceLedgerChunk010Chars00 ++ (faceLedgerChunk011Chars00 ++ (tail)))) := by
    simp only [faceLedgerBlock002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 46)
        (SourceJson.white (faceLedgerBlock002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white (faceLedgerChunk008Chars00 ++ (faceLedgerChunk009Chars00 ++ (faceLedgerChunk010Chars00 ++ (faceLedgerChunk011Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 46) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 45) (SourceJson.white (faceLedgerChunk009Chars00 ++ (faceLedgerChunk010Chars00 ++ (faceLedgerChunk011Chars00 ++ (tail))))) (faceLedgerChunk008Push00 (acc)) := array_faceLedger_chunk_008 fuel (faceLedgerChunk009Chars00 ++ (faceLedgerChunk010Chars00 ++ (faceLedgerChunk011Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 44) (SourceJson.white (faceLedgerChunk010Chars00 ++ (faceLedgerChunk011Chars00 ++ (tail)))) (faceLedgerChunk009Push00 (faceLedgerChunk008Push00 (acc))) := array_faceLedger_chunk_009 fuel (faceLedgerChunk010Chars00 ++ (faceLedgerChunk011Chars00 ++ (tail))) (faceLedgerChunk008Push00 (acc))
    _ = SourceJson.array (fuel + 43) (SourceJson.white (faceLedgerChunk011Chars00 ++ (tail))) (faceLedgerChunk010Push00 (faceLedgerChunk009Push00 (faceLedgerChunk008Push00 (acc)))) := array_faceLedger_chunk_010 fuel (faceLedgerChunk011Chars00 ++ (tail)) (faceLedgerChunk009Push00 (faceLedgerChunk008Push00 (acc)))
    _ = SourceJson.array (fuel + 42) (SourceJson.white tail) (faceLedgerBlock002Push00 acc) := array_faceLedger_chunk_011 fuel (tail) (faceLedgerChunk010Push00 (faceLedgerChunk009Push00 (faceLedgerChunk008Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_002_before_single_binding"
  err.flush

theorem geometryChars00_faceLedger_block_002_prefix :
    (geometryChars00.drop 78904).take 5970 = faceLedgerBlock002Chars00 := by rfl

theorem geometryChars00_faceLedger_block_002_split :
    geometryChars00.drop 78904 = faceLedgerBlock002Chars00 ++ geometryChars00.drop 84874 := by
  calc
    geometryChars00.drop 78904 =
        (geometryChars00.drop 78904).take 5970 ++ (geometryChars00.drop 78904).drop 5970 :=
      (List.take_append_drop 5970 (geometryChars00.drop 78904)).symm
    _ = faceLedgerBlock002Chars00 ++ (geometryChars00.drop 78904).drop 5970 :=
      congrArg (fun p => p ++ (geometryChars00.drop 78904).drop 5970) geometryChars00_faceLedger_block_002_prefix
    _ = faceLedgerBlock002Chars00 ++ geometryChars00.drop 84874 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_002_after_single_binding"
  err.flush

theorem array_faceLedger_original_block_002 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (geometryChars00.drop 78904)) acc =
      SourceJson.array (fuel + 42)
        (SourceJson.white (geometryChars00.drop 84874)) (faceLedgerBlock002Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 46) (SourceJson.white s) acc)
      geometryChars00_faceLedger_block_002_split).trans (array_faceLedger_block_002 fuel (geometryChars00.drop 84874) acc)

theorem faceLedger_array_through_block_002 (fuel : Nat) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) [] =
      SourceJson.array (fuel + 42)
        (SourceJson.white (geometryChars00.drop 84874)) faceLedgerArrayAcc01200 := by
  exact (faceLedger_array_through_block_001 fuel).trans
    (array_faceLedger_original_block_002 fuel faceLedgerArrayAcc00800)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_002_complete"
  err.flush

#print axioms array_faceLedger_chunk_008_head
#print axioms array_faceLedger_chunk_008
#print axioms array_faceLedger_chunk_009_head
#print axioms array_faceLedger_chunk_009
#print axioms array_faceLedger_chunk_010_head
#print axioms array_faceLedger_chunk_010
#print axioms array_faceLedger_chunk_011_head
#print axioms array_faceLedger_chunk_011
#print axioms array_faceLedger_block_002
#print axioms geometryChars00_faceLedger_block_002_prefix
#print axioms geometryChars00_faceLedger_block_002_split
#print axioms array_faceLedger_original_block_002
#print axioms faceLedger_array_through_block_002

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
