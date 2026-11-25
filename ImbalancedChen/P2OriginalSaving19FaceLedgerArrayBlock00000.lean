import ImbalancedChen.P2OriginalSaving19FacetVerticesField00
import ImbalancedChen.P2OriginalSaving19ValueFragment06644800
import ImbalancedChen.P2OriginalSaving19ValueFragment06726500

/-! Original face_ledger block 0/8. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def faceLedgerOpenChars00 : List Char := ['[']
noncomputable def faceLedgerArrayAcc00000 : List SourceJson := []

theorem geometryChars00_faceLedger_open_prefix :
    (geometryChars00.drop 65240).take 1 = faceLedgerOpenChars00 := by rfl

theorem geometryChars00_faceLedger_open_split :
    geometryChars00.drop 65240 = faceLedgerOpenChars00 ++ geometryChars00.drop 65241 := by
  calc
    geometryChars00.drop 65240 =
        (geometryChars00.drop 65240).take 1 ++ (geometryChars00.drop 65240).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 65240)).symm
    _ = faceLedgerOpenChars00 ++ (geometryChars00.drop 65240).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 65240).drop 1) geometryChars00_faceLedger_open_prefix
    _ = faceLedgerOpenChars00 ++ geometryChars00.drop 65241 := by rw [List.drop_drop]

theorem value_faceLedger_open (fuel : Nat) :
    SourceJson.value (fuel + 56) (geometryChars00.drop 65240) =
      SourceJson.array (fuel + 55)
        (SourceJson.white (geometryChars00.drop 65241)) [] := by
  calc
    SourceJson.value (fuel + 56) (geometryChars00.drop 65240) =
        SourceJson.value (fuel + 56)
          (faceLedgerOpenChars00 ++ geometryChars00.drop 65241) :=
      congrArg (SourceJson.value (fuel + 56)) geometryChars00_faceLedger_open_split
    _ = SourceJson.array (fuel + 55)
        (SourceJson.white (geometryChars00.drop 65241)) [] := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_000_before_generic"
  err.flush

noncomputable def faceLedgerChunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_faceLedger_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55) (SourceJson.white (faceLedgerChunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white tail) (faceLedgerChunk000Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc00100 : List SourceJson := faceLedgerChunk000Push00 faceLedgerArrayAcc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_000_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_001_before_generic"
  err.flush

noncomputable def faceLedgerChunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_faceLedger_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53) (SourceJson.white (faceLedgerChunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (faceLedgerChunk001Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc00200 : List SourceJson := faceLedgerChunk001Push00 faceLedgerArrayAcc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_001_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_002_before_generic"
  err.flush

noncomputable def faceLedgerChunk002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk002SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk002Chars00 : List Char := faceLedgerChunk002LeadChars00 ++ fragment066448Chars00 ++ faceLedgerChunk002SuffixChars00
noncomputable def faceLedgerChunk002Push00 (acc : List SourceJson) : List SourceJson := fragment066448Value00 :: acc

noncomputable def faceLedgerChunk002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (faceLedgerChunk002LeadChars00 ++ (fragment066448Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 51) (fragment066448Chars00 ++ rest)).bind
        (faceLedgerChunk002AfterValue00 (fuel + 51) acc) := by rfl

theorem array_faceLedger_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (faceLedgerChunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 51) (SourceJson.white tail) (faceLedgerChunk002Push00 acc) := by
  have hinput : faceLedgerChunk002Chars00 ++ tail = faceLedgerChunk002LeadChars00 ++ (fragment066448Chars00 ++ (faceLedgerChunk002SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 52) (SourceJson.white (faceLedgerChunk002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 52)
          (SourceJson.white (faceLedgerChunk002LeadChars00 ++ (fragment066448Chars00 ++ (faceLedgerChunk002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 52) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 51) (fragment066448Chars00 ++ (faceLedgerChunk002SuffixChars00 ++ tail))).bind
        (faceLedgerChunk002AfterValue00 (fuel + 51) acc) := array_faceLedger_chunk_002_head fuel (faceLedgerChunk002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment066448Value00, faceLedgerChunk002SuffixChars00 ++ tail)).bind
        (faceLedgerChunk002AfterValue00 (fuel + 51) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk002AfterValue00 (fuel + 51) acc))
        (value_fragment066448 (fuel + 31) (faceLedgerChunk002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 51) (SourceJson.white tail) (faceLedgerChunk002Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc00300 : List SourceJson := faceLedgerChunk002Push00 faceLedgerArrayAcc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_002_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_003_before_generic"
  err.flush

noncomputable def faceLedgerChunk003LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk003SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk003Chars00 : List Char := faceLedgerChunk003LeadChars00 ++ fragment067265Chars00 ++ faceLedgerChunk003SuffixChars00
noncomputable def faceLedgerChunk003Push00 (acc : List SourceJson) : List SourceJson := fragment067265Value00 :: acc

noncomputable def faceLedgerChunk003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51)
      (SourceJson.white (faceLedgerChunk003LeadChars00 ++ (fragment067265Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 50) (fragment067265Chars00 ++ rest)).bind
        (faceLedgerChunk003AfterValue00 (fuel + 50) acc) := by rfl

theorem array_faceLedger_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51) (SourceJson.white (faceLedgerChunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (faceLedgerChunk003Push00 acc) := by
  have hinput : faceLedgerChunk003Chars00 ++ tail = faceLedgerChunk003LeadChars00 ++ (fragment067265Chars00 ++ (faceLedgerChunk003SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 51) (SourceJson.white (faceLedgerChunk003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 51)
          (SourceJson.white (faceLedgerChunk003LeadChars00 ++ (fragment067265Chars00 ++ (faceLedgerChunk003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 51) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 50) (fragment067265Chars00 ++ (faceLedgerChunk003SuffixChars00 ++ tail))).bind
        (faceLedgerChunk003AfterValue00 (fuel + 50) acc) := array_faceLedger_chunk_003_head fuel (faceLedgerChunk003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment067265Value00, faceLedgerChunk003SuffixChars00 ++ tail)).bind
        (faceLedgerChunk003AfterValue00 (fuel + 50) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk003AfterValue00 (fuel + 50) acc))
        (value_fragment067265 (fuel + 27) (faceLedgerChunk003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 50) (SourceJson.white tail) (faceLedgerChunk003Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc00400 : List SourceJson := faceLedgerChunk003Push00 faceLedgerArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_003_generic_complete"
  err.flush

noncomputable def faceLedgerBlock000Chars00 : List Char := faceLedgerChunk000Chars00 ++ faceLedgerChunk001Chars00 ++ faceLedgerChunk002Chars00 ++ faceLedgerChunk003Chars00
noncomputable def faceLedgerBlock000Push00 (acc : List SourceJson) : List SourceJson := faceLedgerChunk003Push00 (faceLedgerChunk002Push00 (faceLedgerChunk001Push00 (faceLedgerChunk000Push00 (acc))))

theorem array_faceLedger_block_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (faceLedgerBlock000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (faceLedgerBlock000Push00 acc) := by
  have hinput : faceLedgerBlock000Chars00 ++ tail = faceLedgerChunk000Chars00 ++ (faceLedgerChunk001Chars00 ++ (faceLedgerChunk002Chars00 ++ (faceLedgerChunk003Chars00 ++ (tail)))) := by
    simp only [faceLedgerBlock000Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 55)
        (SourceJson.white (faceLedgerBlock000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white (faceLedgerChunk000Chars00 ++ (faceLedgerChunk001Chars00 ++ (faceLedgerChunk002Chars00 ++ (faceLedgerChunk003Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 55) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 53) (SourceJson.white (faceLedgerChunk001Chars00 ++ (faceLedgerChunk002Chars00 ++ (faceLedgerChunk003Chars00 ++ (tail))))) (faceLedgerChunk000Push00 (acc)) := array_faceLedger_chunk_000 fuel (faceLedgerChunk001Chars00 ++ (faceLedgerChunk002Chars00 ++ (faceLedgerChunk003Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 52) (SourceJson.white (faceLedgerChunk002Chars00 ++ (faceLedgerChunk003Chars00 ++ (tail)))) (faceLedgerChunk001Push00 (faceLedgerChunk000Push00 (acc))) := array_faceLedger_chunk_001 fuel (faceLedgerChunk002Chars00 ++ (faceLedgerChunk003Chars00 ++ (tail))) (faceLedgerChunk000Push00 (acc))
    _ = SourceJson.array (fuel + 51) (SourceJson.white (faceLedgerChunk003Chars00 ++ (tail))) (faceLedgerChunk002Push00 (faceLedgerChunk001Push00 (faceLedgerChunk000Push00 (acc)))) := array_faceLedger_chunk_002 fuel (faceLedgerChunk003Chars00 ++ (tail)) (faceLedgerChunk001Push00 (faceLedgerChunk000Push00 (acc)))
    _ = SourceJson.array (fuel + 50) (SourceJson.white tail) (faceLedgerBlock000Push00 acc) := array_faceLedger_chunk_003 fuel (tail) (faceLedgerChunk002Push00 (faceLedgerChunk001Push00 (faceLedgerChunk000Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_000_before_single_binding"
  err.flush

theorem geometryChars00_faceLedger_block_000_prefix :
    (geometryChars00.drop 65241).take 3133 = faceLedgerBlock000Chars00 := by rfl

theorem geometryChars00_faceLedger_block_000_split :
    geometryChars00.drop 65241 = faceLedgerBlock000Chars00 ++ geometryChars00.drop 68374 := by
  calc
    geometryChars00.drop 65241 =
        (geometryChars00.drop 65241).take 3133 ++ (geometryChars00.drop 65241).drop 3133 :=
      (List.take_append_drop 3133 (geometryChars00.drop 65241)).symm
    _ = faceLedgerBlock000Chars00 ++ (geometryChars00.drop 65241).drop 3133 :=
      congrArg (fun p => p ++ (geometryChars00.drop 65241).drop 3133) geometryChars00_faceLedger_block_000_prefix
    _ = faceLedgerBlock000Chars00 ++ geometryChars00.drop 68374 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_000_after_single_binding"
  err.flush

theorem array_faceLedger_original_block_000 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) acc =
      SourceJson.array (fuel + 50)
        (SourceJson.white (geometryChars00.drop 68374)) (faceLedgerBlock000Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 55) (SourceJson.white s) acc)
      geometryChars00_faceLedger_block_000_split).trans (array_faceLedger_block_000 fuel (geometryChars00.drop 68374) acc)

theorem faceLedger_array_through_block_000 (fuel : Nat) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) [] =
      SourceJson.array (fuel + 50)
        (SourceJson.white (geometryChars00.drop 68374)) faceLedgerArrayAcc00400 := by
  exact array_faceLedger_original_block_000 fuel faceLedgerArrayAcc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_000_complete"
  err.flush

#print axioms geometryChars00_faceLedger_open_prefix
#print axioms geometryChars00_faceLedger_open_split
#print axioms value_faceLedger_open
#print axioms array_faceLedger_chunk_000
#print axioms array_faceLedger_chunk_001
#print axioms array_faceLedger_chunk_002_head
#print axioms array_faceLedger_chunk_002
#print axioms array_faceLedger_chunk_003_head
#print axioms array_faceLedger_chunk_003
#print axioms array_faceLedger_block_000
#print axioms geometryChars00_faceLedger_block_000_prefix
#print axioms geometryChars00_faceLedger_block_000_split
#print axioms array_faceLedger_original_block_000
#print axioms faceLedger_array_through_block_000

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
