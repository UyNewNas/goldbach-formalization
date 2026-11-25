import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00200
import ImbalancedChen.P2OriginalSaving19ValueFragment08661100

/-! Original face_ledger block 3/8. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_012_before_generic"
  err.flush

noncomputable def faceLedgerChunk012Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk012Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '8'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['6']))]) :: (acc)

theorem array_faceLedger_chunk_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42) (SourceJson.white (faceLedgerChunk012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (faceLedgerChunk012Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc01300 : List SourceJson := faceLedgerChunk012Push00 faceLedgerArrayAcc01200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_012_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_013_before_generic"
  err.flush

noncomputable def faceLedgerChunk013Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk013Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_faceLedger_chunk_013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41) (SourceJson.white (faceLedgerChunk013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 39) (SourceJson.white tail) (faceLedgerChunk013Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc01400 : List SourceJson := faceLedgerChunk013Push00 faceLedgerArrayAcc01300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_013_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_014_before_generic"
  err.flush

noncomputable def faceLedgerChunk014Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk014Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['9'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['9'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['9'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_faceLedger_chunk_014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39) (SourceJson.white (faceLedgerChunk014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail) (faceLedgerChunk014Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc01500 : List SourceJson := faceLedgerChunk014Push00 faceLedgerArrayAcc01400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_014_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_015_before_generic"
  err.flush

noncomputable def faceLedgerChunk015LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk015SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk015Chars00 : List Char := faceLedgerChunk015LeadChars00 ++ fragment086611Chars00 ++ faceLedgerChunk015SuffixChars00
noncomputable def faceLedgerChunk015Push00 (acc : List SourceJson) : List SourceJson := fragment086611Value00 :: acc

noncomputable def faceLedgerChunk015AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_015_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (faceLedgerChunk015LeadChars00 ++ (fragment086611Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 37) (fragment086611Chars00 ++ rest)).bind
        (faceLedgerChunk015AfterValue00 (fuel + 37) acc) := by rfl

theorem array_faceLedger_chunk_015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38) (SourceJson.white (faceLedgerChunk015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 37) (SourceJson.white tail) (faceLedgerChunk015Push00 acc) := by
  have hinput : faceLedgerChunk015Chars00 ++ tail = faceLedgerChunk015LeadChars00 ++ (fragment086611Chars00 ++ (faceLedgerChunk015SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk015Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 38) (SourceJson.white (faceLedgerChunk015Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 38)
          (SourceJson.white (faceLedgerChunk015LeadChars00 ++ (fragment086611Chars00 ++ (faceLedgerChunk015SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 38) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 37) (fragment086611Chars00 ++ (faceLedgerChunk015SuffixChars00 ++ tail))).bind
        (faceLedgerChunk015AfterValue00 (fuel + 37) acc) := array_faceLedger_chunk_015_head fuel (faceLedgerChunk015SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment086611Value00, faceLedgerChunk015SuffixChars00 ++ tail)).bind
        (faceLedgerChunk015AfterValue00 (fuel + 37) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk015AfterValue00 (fuel + 37) acc))
        (value_fragment086611 (fuel + 18) (faceLedgerChunk015SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 37) (SourceJson.white tail) (faceLedgerChunk015Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc01600 : List SourceJson := faceLedgerChunk015Push00 faceLedgerArrayAcc01500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_015_generic_complete"
  err.flush

noncomputable def faceLedgerBlock003Chars00 : List Char := faceLedgerChunk012Chars00 ++ faceLedgerChunk013Chars00 ++ faceLedgerChunk014Chars00 ++ faceLedgerChunk015Chars00
noncomputable def faceLedgerBlock003Push00 (acc : List SourceJson) : List SourceJson := faceLedgerChunk015Push00 (faceLedgerChunk014Push00 (faceLedgerChunk013Push00 (faceLedgerChunk012Push00 (acc))))

theorem array_faceLedger_block_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (faceLedgerBlock003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 37) (SourceJson.white tail) (faceLedgerBlock003Push00 acc) := by
  have hinput : faceLedgerBlock003Chars00 ++ tail = faceLedgerChunk012Chars00 ++ (faceLedgerChunk013Chars00 ++ (faceLedgerChunk014Chars00 ++ (faceLedgerChunk015Chars00 ++ (tail)))) := by
    simp only [faceLedgerBlock003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 42)
        (SourceJson.white (faceLedgerBlock003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white (faceLedgerChunk012Chars00 ++ (faceLedgerChunk013Chars00 ++ (faceLedgerChunk014Chars00 ++ (faceLedgerChunk015Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 42) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 41) (SourceJson.white (faceLedgerChunk013Chars00 ++ (faceLedgerChunk014Chars00 ++ (faceLedgerChunk015Chars00 ++ (tail))))) (faceLedgerChunk012Push00 (acc)) := array_faceLedger_chunk_012 fuel (faceLedgerChunk013Chars00 ++ (faceLedgerChunk014Chars00 ++ (faceLedgerChunk015Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 39) (SourceJson.white (faceLedgerChunk014Chars00 ++ (faceLedgerChunk015Chars00 ++ (tail)))) (faceLedgerChunk013Push00 (faceLedgerChunk012Push00 (acc))) := array_faceLedger_chunk_013 fuel (faceLedgerChunk014Chars00 ++ (faceLedgerChunk015Chars00 ++ (tail))) (faceLedgerChunk012Push00 (acc))
    _ = SourceJson.array (fuel + 38) (SourceJson.white (faceLedgerChunk015Chars00 ++ (tail))) (faceLedgerChunk014Push00 (faceLedgerChunk013Push00 (faceLedgerChunk012Push00 (acc)))) := array_faceLedger_chunk_014 fuel (faceLedgerChunk015Chars00 ++ (tail)) (faceLedgerChunk013Push00 (faceLedgerChunk012Push00 (acc)))
    _ = SourceJson.array (fuel + 37) (SourceJson.white tail) (faceLedgerBlock003Push00 acc) := array_faceLedger_chunk_015 fuel (tail) (faceLedgerChunk014Push00 (faceLedgerChunk013Push00 (faceLedgerChunk012Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_003_before_single_binding"
  err.flush

theorem geometryChars00_faceLedger_block_003_prefix :
    (geometryChars00.drop 84874).take 2569 = faceLedgerBlock003Chars00 := by rfl

theorem geometryChars00_faceLedger_block_003_split :
    geometryChars00.drop 84874 = faceLedgerBlock003Chars00 ++ geometryChars00.drop 87443 := by
  calc
    geometryChars00.drop 84874 =
        (geometryChars00.drop 84874).take 2569 ++ (geometryChars00.drop 84874).drop 2569 :=
      (List.take_append_drop 2569 (geometryChars00.drop 84874)).symm
    _ = faceLedgerBlock003Chars00 ++ (geometryChars00.drop 84874).drop 2569 :=
      congrArg (fun p => p ++ (geometryChars00.drop 84874).drop 2569) geometryChars00_faceLedger_block_003_prefix
    _ = faceLedgerBlock003Chars00 ++ geometryChars00.drop 87443 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_003_after_single_binding"
  err.flush

theorem array_faceLedger_original_block_003 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (geometryChars00.drop 84874)) acc =
      SourceJson.array (fuel + 37)
        (SourceJson.white (geometryChars00.drop 87443)) (faceLedgerBlock003Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 42) (SourceJson.white s) acc)
      geometryChars00_faceLedger_block_003_split).trans (array_faceLedger_block_003 fuel (geometryChars00.drop 87443) acc)

theorem faceLedger_array_through_block_003 (fuel : Nat) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) [] =
      SourceJson.array (fuel + 37)
        (SourceJson.white (geometryChars00.drop 87443)) faceLedgerArrayAcc01600 := by
  exact (faceLedger_array_through_block_002 fuel).trans
    (array_faceLedger_original_block_003 fuel faceLedgerArrayAcc01200)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_003_complete"
  err.flush

#print axioms array_faceLedger_chunk_012
#print axioms array_faceLedger_chunk_013
#print axioms array_faceLedger_chunk_014
#print axioms array_faceLedger_chunk_015_head
#print axioms array_faceLedger_chunk_015
#print axioms array_faceLedger_block_003
#print axioms geometryChars00_faceLedger_block_003_prefix
#print axioms geometryChars00_faceLedger_block_003_split
#print axioms array_faceLedger_original_block_003
#print axioms faceLedger_array_through_block_003

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
