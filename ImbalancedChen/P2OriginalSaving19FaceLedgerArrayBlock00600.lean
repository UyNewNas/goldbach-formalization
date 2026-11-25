import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00500
import ImbalancedChen.P2OriginalSaving19ValueFragment09427600
import ImbalancedChen.P2OriginalSaving19ValueFragment09525800
import ImbalancedChen.P2OriginalSaving19ValueFragment09684900

/-! Original face_ledger block 6/8. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_024_before_generic"
  err.flush

noncomputable def faceLedgerChunk024LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk024SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk024Chars00 : List Char := faceLedgerChunk024LeadChars00 ++ fragment094276Chars00 ++ faceLedgerChunk024SuffixChars00
noncomputable def faceLedgerChunk024Push00 (acc : List SourceJson) : List SourceJson := fragment094276Value00 :: acc

noncomputable def faceLedgerChunk024AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_024_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28)
      (SourceJson.white (faceLedgerChunk024LeadChars00 ++ (fragment094276Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 27) (fragment094276Chars00 ++ rest)).bind
        (faceLedgerChunk024AfterValue00 (fuel + 27) acc) := by rfl

theorem array_faceLedger_chunk_024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (faceLedgerChunk024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 27) (SourceJson.white tail) (faceLedgerChunk024Push00 acc) := by
  have hinput : faceLedgerChunk024Chars00 ++ tail = faceLedgerChunk024LeadChars00 ++ (fragment094276Chars00 ++ (faceLedgerChunk024SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk024Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 28) (SourceJson.white (faceLedgerChunk024Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 28)
          (SourceJson.white (faceLedgerChunk024LeadChars00 ++ (fragment094276Chars00 ++ (faceLedgerChunk024SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 28) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 27) (fragment094276Chars00 ++ (faceLedgerChunk024SuffixChars00 ++ tail))).bind
        (faceLedgerChunk024AfterValue00 (fuel + 27) acc) := array_faceLedger_chunk_024_head fuel (faceLedgerChunk024SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment094276Value00, faceLedgerChunk024SuffixChars00 ++ tail)).bind
        (faceLedgerChunk024AfterValue00 (fuel + 27) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk024AfterValue00 (fuel + 27) acc))
        (value_fragment094276 (fuel + 6) (faceLedgerChunk024SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 27) (SourceJson.white tail) (faceLedgerChunk024Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc02500 : List SourceJson := faceLedgerChunk024Push00 faceLedgerArrayAcc02400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_024_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_025_before_generic"
  err.flush

noncomputable def faceLedgerChunk025LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk025SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk025Chars00 : List Char := faceLedgerChunk025LeadChars00 ++ fragment095258Chars00 ++ faceLedgerChunk025SuffixChars00
noncomputable def faceLedgerChunk025Push00 (acc : List SourceJson) : List SourceJson := fragment095258Value00 :: acc

noncomputable def faceLedgerChunk025AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_025_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27)
      (SourceJson.white (faceLedgerChunk025LeadChars00 ++ (fragment095258Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 26) (fragment095258Chars00 ++ rest)).bind
        (faceLedgerChunk025AfterValue00 (fuel + 26) acc) := by rfl

theorem array_faceLedger_chunk_025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (faceLedgerChunk025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 26) (SourceJson.white tail) (faceLedgerChunk025Push00 acc) := by
  have hinput : faceLedgerChunk025Chars00 ++ tail = faceLedgerChunk025LeadChars00 ++ (fragment095258Chars00 ++ (faceLedgerChunk025SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk025Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 27) (SourceJson.white (faceLedgerChunk025Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 27)
          (SourceJson.white (faceLedgerChunk025LeadChars00 ++ (fragment095258Chars00 ++ (faceLedgerChunk025SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 27) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 26) (fragment095258Chars00 ++ (faceLedgerChunk025SuffixChars00 ++ tail))).bind
        (faceLedgerChunk025AfterValue00 (fuel + 26) acc) := array_faceLedger_chunk_025_head fuel (faceLedgerChunk025SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment095258Value00, faceLedgerChunk025SuffixChars00 ++ tail)).bind
        (faceLedgerChunk025AfterValue00 (fuel + 26) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk025AfterValue00 (fuel + 26) acc))
        (value_fragment095258 (fuel + 4) (faceLedgerChunk025SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 26) (SourceJson.white tail) (faceLedgerChunk025Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc02600 : List SourceJson := faceLedgerChunk025Push00 faceLedgerArrayAcc02500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_025_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_026_before_generic"
  err.flush

noncomputable def faceLedgerChunk026Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk026Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['8'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_faceLedger_chunk_026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (faceLedgerChunk026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (faceLedgerChunk026Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc02700 : List SourceJson := faceLedgerChunk026Push00 faceLedgerArrayAcc02600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_026_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_027_before_generic"
  err.flush

noncomputable def faceLedgerChunk027LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk027SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk027Chars00 : List Char := faceLedgerChunk027LeadChars00 ++ fragment096849Chars00 ++ faceLedgerChunk027SuffixChars00
noncomputable def faceLedgerChunk027Push00 (acc : List SourceJson) : List SourceJson := fragment096849Value00 :: acc

noncomputable def faceLedgerChunk027AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_027_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25)
      (SourceJson.white (faceLedgerChunk027LeadChars00 ++ (fragment096849Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 24) (fragment096849Chars00 ++ rest)).bind
        (faceLedgerChunk027AfterValue00 (fuel + 24) acc) := by rfl

theorem array_faceLedger_chunk_027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (faceLedgerChunk027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (faceLedgerChunk027Push00 acc) := by
  have hinput : faceLedgerChunk027Chars00 ++ tail = faceLedgerChunk027LeadChars00 ++ (fragment096849Chars00 ++ (faceLedgerChunk027SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk027Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 25) (SourceJson.white (faceLedgerChunk027Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 25)
          (SourceJson.white (faceLedgerChunk027LeadChars00 ++ (fragment096849Chars00 ++ (faceLedgerChunk027SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 25) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 24) (fragment096849Chars00 ++ (faceLedgerChunk027SuffixChars00 ++ tail))).bind
        (faceLedgerChunk027AfterValue00 (fuel + 24) acc) := array_faceLedger_chunk_027_head fuel (faceLedgerChunk027SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment096849Value00, faceLedgerChunk027SuffixChars00 ++ tail)).bind
        (faceLedgerChunk027AfterValue00 (fuel + 24) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk027AfterValue00 (fuel + 24) acc))
        (value_fragment096849 (fuel + 5) (faceLedgerChunk027SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 24) (SourceJson.white tail) (faceLedgerChunk027Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc02800 : List SourceJson := faceLedgerChunk027Push00 faceLedgerArrayAcc02700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_027_generic_complete"
  err.flush

noncomputable def faceLedgerBlock006Chars00 : List Char := faceLedgerChunk024Chars00 ++ faceLedgerChunk025Chars00 ++ faceLedgerChunk026Chars00 ++ faceLedgerChunk027Chars00
noncomputable def faceLedgerBlock006Push00 (acc : List SourceJson) : List SourceJson := faceLedgerChunk027Push00 (faceLedgerChunk026Push00 (faceLedgerChunk025Push00 (faceLedgerChunk024Push00 (acc))))

theorem array_faceLedger_block_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28)
      (SourceJson.white (faceLedgerBlock006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (faceLedgerBlock006Push00 acc) := by
  have hinput : faceLedgerBlock006Chars00 ++ tail = faceLedgerChunk024Chars00 ++ (faceLedgerChunk025Chars00 ++ (faceLedgerChunk026Chars00 ++ (faceLedgerChunk027Chars00 ++ (tail)))) := by
    simp only [faceLedgerBlock006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 28)
        (SourceJson.white (faceLedgerBlock006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white (faceLedgerChunk024Chars00 ++ (faceLedgerChunk025Chars00 ++ (faceLedgerChunk026Chars00 ++ (faceLedgerChunk027Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 28) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 27) (SourceJson.white (faceLedgerChunk025Chars00 ++ (faceLedgerChunk026Chars00 ++ (faceLedgerChunk027Chars00 ++ (tail))))) (faceLedgerChunk024Push00 (acc)) := array_faceLedger_chunk_024 fuel (faceLedgerChunk025Chars00 ++ (faceLedgerChunk026Chars00 ++ (faceLedgerChunk027Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 26) (SourceJson.white (faceLedgerChunk026Chars00 ++ (faceLedgerChunk027Chars00 ++ (tail)))) (faceLedgerChunk025Push00 (faceLedgerChunk024Push00 (acc))) := array_faceLedger_chunk_025 fuel (faceLedgerChunk026Chars00 ++ (faceLedgerChunk027Chars00 ++ (tail))) (faceLedgerChunk024Push00 (acc))
    _ = SourceJson.array (fuel + 25) (SourceJson.white (faceLedgerChunk027Chars00 ++ (tail))) (faceLedgerChunk026Push00 (faceLedgerChunk025Push00 (faceLedgerChunk024Push00 (acc)))) := array_faceLedger_chunk_026 fuel (faceLedgerChunk027Chars00 ++ (tail)) (faceLedgerChunk025Push00 (faceLedgerChunk024Push00 (acc)))
    _ = SourceJson.array (fuel + 24) (SourceJson.white tail) (faceLedgerBlock006Push00 acc) := array_faceLedger_chunk_027 fuel (tail) (faceLedgerChunk026Push00 (faceLedgerChunk025Push00 (faceLedgerChunk024Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_006_before_single_binding"
  err.flush

theorem geometryChars00_faceLedger_block_006_prefix :
    (geometryChars00.drop 94270).take 3411 = faceLedgerBlock006Chars00 := by rfl

theorem geometryChars00_faceLedger_block_006_split :
    geometryChars00.drop 94270 = faceLedgerBlock006Chars00 ++ geometryChars00.drop 97681 := by
  calc
    geometryChars00.drop 94270 =
        (geometryChars00.drop 94270).take 3411 ++ (geometryChars00.drop 94270).drop 3411 :=
      (List.take_append_drop 3411 (geometryChars00.drop 94270)).symm
    _ = faceLedgerBlock006Chars00 ++ (geometryChars00.drop 94270).drop 3411 :=
      congrArg (fun p => p ++ (geometryChars00.drop 94270).drop 3411) geometryChars00_faceLedger_block_006_prefix
    _ = faceLedgerBlock006Chars00 ++ geometryChars00.drop 97681 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_006_after_single_binding"
  err.flush

theorem array_faceLedger_original_block_006 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 28)
      (SourceJson.white (geometryChars00.drop 94270)) acc =
      SourceJson.array (fuel + 24)
        (SourceJson.white (geometryChars00.drop 97681)) (faceLedgerBlock006Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 28) (SourceJson.white s) acc)
      geometryChars00_faceLedger_block_006_split).trans (array_faceLedger_block_006 fuel (geometryChars00.drop 97681) acc)

theorem faceLedger_array_through_block_006 (fuel : Nat) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) [] =
      SourceJson.array (fuel + 24)
        (SourceJson.white (geometryChars00.drop 97681)) faceLedgerArrayAcc02800 := by
  exact (faceLedger_array_through_block_005 fuel).trans
    (array_faceLedger_original_block_006 fuel faceLedgerArrayAcc02400)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_006_complete"
  err.flush

#print axioms array_faceLedger_chunk_024_head
#print axioms array_faceLedger_chunk_024
#print axioms array_faceLedger_chunk_025_head
#print axioms array_faceLedger_chunk_025
#print axioms array_faceLedger_chunk_026
#print axioms array_faceLedger_chunk_027_head
#print axioms array_faceLedger_chunk_027
#print axioms array_faceLedger_block_006
#print axioms geometryChars00_faceLedger_block_006_prefix
#print axioms geometryChars00_faceLedger_block_006_split
#print axioms array_faceLedger_original_block_006
#print axioms faceLedger_array_through_block_006

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
