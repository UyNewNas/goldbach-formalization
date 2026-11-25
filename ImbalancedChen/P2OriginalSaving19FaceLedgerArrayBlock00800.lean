import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00700

/-! Original face_ledger block 8/8. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_032_before_generic"
  err.flush

noncomputable def faceLedgerChunk032Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def faceLedgerChunk032Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['3']), .number (String.ofList ['1', '3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['3'])], .arr [.number (String.ofList ['1', '3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_faceLedger_chunk_032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (faceLedgerChunk032Chars00 ++ tail)) acc =
      .ok (.arr ((faceLedgerChunk032Push00 acc).reverse), tail) := by
  rfl

noncomputable def faceLedgerArrayAcc03300 : List SourceJson := faceLedgerChunk032Push00 faceLedgerArrayAcc03200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_032_generic_complete"
  err.flush

noncomputable def faceLedgerBlock008Chars00 : List Char := faceLedgerChunk032Chars00
noncomputable def faceLedgerBlock008Push00 (acc : List SourceJson) : List SourceJson := faceLedgerChunk032Push00 (acc)

theorem array_faceLedger_block_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17)
      (SourceJson.white (faceLedgerBlock008Chars00 ++ tail)) acc =
      .ok (.arr ((faceLedgerBlock008Push00 acc).reverse), tail) := by
  have hinput : faceLedgerBlock008Chars00 ++ tail = faceLedgerChunk032Chars00 ++ (tail) := by
    simp only [faceLedgerBlock008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 17)
        (SourceJson.white (faceLedgerBlock008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white (faceLedgerChunk032Chars00 ++ (tail))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 17) (SourceJson.white s) acc) hinput
    _ = .ok (.arr ((faceLedgerBlock008Push00 acc).reverse), tail) := array_faceLedger_chunk_032 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_008_before_single_binding"
  err.flush

theorem geometryChars00_faceLedger_block_008_prefix :
    (geometryChars00.drop 100171).take 244 = faceLedgerBlock008Chars00 := by rfl

theorem geometryChars00_faceLedger_block_008_split :
    geometryChars00.drop 100171 = faceLedgerBlock008Chars00 ++ geometryChars00.drop 100415 := by
  calc
    geometryChars00.drop 100171 =
        (geometryChars00.drop 100171).take 244 ++ (geometryChars00.drop 100171).drop 244 :=
      (List.take_append_drop 244 (geometryChars00.drop 100171)).symm
    _ = faceLedgerBlock008Chars00 ++ (geometryChars00.drop 100171).drop 244 :=
      congrArg (fun p => p ++ (geometryChars00.drop 100171).drop 244) geometryChars00_faceLedger_block_008_prefix
    _ = faceLedgerBlock008Chars00 ++ geometryChars00.drop 100415 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_008_after_single_binding"
  err.flush

theorem array_faceLedger_original_block_008 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 17)
      (SourceJson.white (geometryChars00.drop 100171)) acc =
      .ok (.arr ((faceLedgerBlock008Push00 acc).reverse), geometryChars00.drop 100415) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 17) (SourceJson.white s) acc)
      geometryChars00_faceLedger_block_008_split).trans (array_faceLedger_block_008 fuel (geometryChars00.drop 100415) acc)

noncomputable def faceLedgerArrayValue00 : SourceJson := .arr (faceLedgerArrayAcc03300.reverse)

theorem faceLedger_array_through_block_008 (fuel : Nat) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) [] =
      .ok (faceLedgerArrayValue00, geometryChars00.drop 100415) := by
  exact (faceLedger_array_through_block_007 fuel).trans
    (array_faceLedger_original_block_008 fuel faceLedgerArrayAcc03200)

theorem value_faceLedger_original (fuel : Nat) :
    SourceJson.value (fuel + 56) (geometryChars00.drop 65240) =
      .ok (faceLedgerArrayValue00, geometryChars00.drop 100415) := by
  exact (value_faceLedger_open fuel).trans (faceLedger_array_through_block_008 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_008_complete"
  err.flush

#print axioms array_faceLedger_chunk_032
#print axioms array_faceLedger_block_008
#print axioms geometryChars00_faceLedger_block_008_prefix
#print axioms geometryChars00_faceLedger_block_008_split
#print axioms array_faceLedger_original_block_008
#print axioms faceLedger_array_through_block_008
#print axioms value_faceLedger_original

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
