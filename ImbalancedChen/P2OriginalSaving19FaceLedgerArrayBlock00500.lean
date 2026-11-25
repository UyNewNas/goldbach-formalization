import ImbalancedChen.P2OriginalSaving19FaceLedgerArrayBlock00400
import ImbalancedChen.P2OriginalSaving19ValueFragment09003300
import ImbalancedChen.P2OriginalSaving19ValueFragment09080500
import ImbalancedChen.P2OriginalSaving19ValueFragment09275700

/-! Original face_ledger block 5/8. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_020_before_generic"
  err.flush

noncomputable def faceLedgerChunk020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk020Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['8'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_faceLedger_chunk_020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32) (SourceJson.white (faceLedgerChunk020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 31) (SourceJson.white tail) (faceLedgerChunk020Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc02100 : List SourceJson := faceLedgerChunk020Push00 faceLedgerArrayAcc02000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_020_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_021_before_generic"
  err.flush

noncomputable def faceLedgerChunk021Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def faceLedgerChunk021Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['5'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_faceLedger_chunk_021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31) (SourceJson.white (faceLedgerChunk021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 30) (SourceJson.white tail) (faceLedgerChunk021Push00 acc) := by
  rfl

noncomputable def faceLedgerArrayAcc02200 : List SourceJson := faceLedgerChunk021Push00 faceLedgerArrayAcc02100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_021_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_022_before_generic"
  err.flush

noncomputable def faceLedgerChunk022LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk022SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk022Chars00 : List Char := faceLedgerChunk022LeadChars00 ++ fragment090805Chars00 ++ faceLedgerChunk022SuffixChars00
noncomputable def faceLedgerChunk022Push00 (acc : List SourceJson) : List SourceJson := fragment090805Value00 :: acc

noncomputable def faceLedgerChunk022AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_022_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30)
      (SourceJson.white (faceLedgerChunk022LeadChars00 ++ (fragment090805Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 29) (fragment090805Chars00 ++ rest)).bind
        (faceLedgerChunk022AfterValue00 (fuel + 29) acc) := by rfl

theorem array_faceLedger_chunk_022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30) (SourceJson.white (faceLedgerChunk022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail) (faceLedgerChunk022Push00 acc) := by
  have hinput : faceLedgerChunk022Chars00 ++ tail = faceLedgerChunk022LeadChars00 ++ (fragment090805Chars00 ++ (faceLedgerChunk022SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk022Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 30) (SourceJson.white (faceLedgerChunk022Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 30)
          (SourceJson.white (faceLedgerChunk022LeadChars00 ++ (fragment090805Chars00 ++ (faceLedgerChunk022SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 30) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 29) (fragment090805Chars00 ++ (faceLedgerChunk022SuffixChars00 ++ tail))).bind
        (faceLedgerChunk022AfterValue00 (fuel + 29) acc) := array_faceLedger_chunk_022_head fuel (faceLedgerChunk022SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment090805Value00, faceLedgerChunk022SuffixChars00 ++ tail)).bind
        (faceLedgerChunk022AfterValue00 (fuel + 29) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk022AfterValue00 (fuel + 29) acc))
        (value_fragment090805 (fuel + 1) (faceLedgerChunk022SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 29) (SourceJson.white tail) (faceLedgerChunk022Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc02300 : List SourceJson := faceLedgerChunk022Push00 faceLedgerArrayAcc02200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_022_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_023_before_generic"
  err.flush

noncomputable def faceLedgerChunk023LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def faceLedgerChunk023SuffixChars00 : List Char := [',']
noncomputable def faceLedgerChunk023Chars00 : List Char := faceLedgerChunk023LeadChars00 ++ fragment092757Chars00 ++ faceLedgerChunk023SuffixChars00
noncomputable def faceLedgerChunk023Push00 (acc : List SourceJson) : List SourceJson := fragment092757Value00 :: acc

noncomputable def faceLedgerChunk023AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_faceLedger_chunk_023_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29)
      (SourceJson.white (faceLedgerChunk023LeadChars00 ++ (fragment092757Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 28) (fragment092757Chars00 ++ rest)).bind
        (faceLedgerChunk023AfterValue00 (fuel + 28) acc) := by rfl

theorem array_faceLedger_chunk_023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (faceLedgerChunk023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white tail) (faceLedgerChunk023Push00 acc) := by
  have hinput : faceLedgerChunk023Chars00 ++ tail = faceLedgerChunk023LeadChars00 ++ (fragment092757Chars00 ++ (faceLedgerChunk023SuffixChars00 ++ tail)) := by
    simp only [faceLedgerChunk023Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 29) (SourceJson.white (faceLedgerChunk023Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 29)
          (SourceJson.white (faceLedgerChunk023LeadChars00 ++ (fragment092757Chars00 ++ (faceLedgerChunk023SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 29) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 28) (fragment092757Chars00 ++ (faceLedgerChunk023SuffixChars00 ++ tail))).bind
        (faceLedgerChunk023AfterValue00 (fuel + 28) acc) := array_faceLedger_chunk_023_head fuel (faceLedgerChunk023SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment092757Value00, faceLedgerChunk023SuffixChars00 ++ tail)).bind
        (faceLedgerChunk023AfterValue00 (fuel + 28) acc) :=
      congrArg (fun result => result.bind (faceLedgerChunk023AfterValue00 (fuel + 28) acc))
        (value_fragment092757 (fuel + 3) (faceLedgerChunk023SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 28) (SourceJson.white tail) (faceLedgerChunk023Push00 acc) := by rfl

noncomputable def faceLedgerArrayAcc02400 : List SourceJson := faceLedgerChunk023Push00 faceLedgerArrayAcc02300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_chunk_023_generic_complete"
  err.flush

noncomputable def faceLedgerBlock005Chars00 : List Char := faceLedgerChunk020Chars00 ++ faceLedgerChunk021Chars00 ++ faceLedgerChunk022Chars00 ++ faceLedgerChunk023Chars00
noncomputable def faceLedgerBlock005Push00 (acc : List SourceJson) : List SourceJson := faceLedgerChunk023Push00 (faceLedgerChunk022Push00 (faceLedgerChunk021Push00 (faceLedgerChunk020Push00 (acc))))

theorem array_faceLedger_block_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32)
      (SourceJson.white (faceLedgerBlock005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white tail) (faceLedgerBlock005Push00 acc) := by
  have hinput : faceLedgerBlock005Chars00 ++ tail = faceLedgerChunk020Chars00 ++ (faceLedgerChunk021Chars00 ++ (faceLedgerChunk022Chars00 ++ (faceLedgerChunk023Chars00 ++ (tail)))) := by
    simp only [faceLedgerBlock005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 32)
        (SourceJson.white (faceLedgerBlock005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white (faceLedgerChunk020Chars00 ++ (faceLedgerChunk021Chars00 ++ (faceLedgerChunk022Chars00 ++ (faceLedgerChunk023Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 32) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 31) (SourceJson.white (faceLedgerChunk021Chars00 ++ (faceLedgerChunk022Chars00 ++ (faceLedgerChunk023Chars00 ++ (tail))))) (faceLedgerChunk020Push00 (acc)) := array_faceLedger_chunk_020 fuel (faceLedgerChunk021Chars00 ++ (faceLedgerChunk022Chars00 ++ (faceLedgerChunk023Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 30) (SourceJson.white (faceLedgerChunk022Chars00 ++ (faceLedgerChunk023Chars00 ++ (tail)))) (faceLedgerChunk021Push00 (faceLedgerChunk020Push00 (acc))) := array_faceLedger_chunk_021 fuel (faceLedgerChunk022Chars00 ++ (faceLedgerChunk023Chars00 ++ (tail))) (faceLedgerChunk020Push00 (acc))
    _ = SourceJson.array (fuel + 29) (SourceJson.white (faceLedgerChunk023Chars00 ++ (tail))) (faceLedgerChunk022Push00 (faceLedgerChunk021Push00 (faceLedgerChunk020Push00 (acc)))) := array_faceLedger_chunk_022 fuel (faceLedgerChunk023Chars00 ++ (tail)) (faceLedgerChunk021Push00 (faceLedgerChunk020Push00 (acc)))
    _ = SourceJson.array (fuel + 28) (SourceJson.white tail) (faceLedgerBlock005Push00 acc) := array_faceLedger_chunk_023 fuel (tail) (faceLedgerChunk022Push00 (faceLedgerChunk021Push00 (faceLedgerChunk020Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_005_before_single_binding"
  err.flush

theorem geometryChars00_faceLedger_block_005_prefix :
    (geometryChars00.drop 89436).take 4834 = faceLedgerBlock005Chars00 := by rfl

theorem geometryChars00_faceLedger_block_005_split :
    geometryChars00.drop 89436 = faceLedgerBlock005Chars00 ++ geometryChars00.drop 94270 := by
  calc
    geometryChars00.drop 89436 =
        (geometryChars00.drop 89436).take 4834 ++ (geometryChars00.drop 89436).drop 4834 :=
      (List.take_append_drop 4834 (geometryChars00.drop 89436)).symm
    _ = faceLedgerBlock005Chars00 ++ (geometryChars00.drop 89436).drop 4834 :=
      congrArg (fun p => p ++ (geometryChars00.drop 89436).drop 4834) geometryChars00_faceLedger_block_005_prefix
    _ = faceLedgerBlock005Chars00 ++ geometryChars00.drop 94270 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_005_after_single_binding"
  err.flush

theorem array_faceLedger_original_block_005 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 32)
      (SourceJson.white (geometryChars00.drop 89436)) acc =
      SourceJson.array (fuel + 28)
        (SourceJson.white (geometryChars00.drop 94270)) (faceLedgerBlock005Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 32) (SourceJson.white s) acc)
      geometryChars00_faceLedger_block_005_split).trans (array_faceLedger_block_005 fuel (geometryChars00.drop 94270) acc)

theorem faceLedger_array_through_block_005 (fuel : Nat) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 65241)) [] =
      SourceJson.array (fuel + 28)
        (SourceJson.white (geometryChars00.drop 94270)) faceLedgerArrayAcc02400 := by
  exact (faceLedger_array_through_block_004 fuel).trans
    (array_faceLedger_original_block_005 fuel faceLedgerArrayAcc02000)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 faceLedger_block_005_complete"
  err.flush

#print axioms array_faceLedger_chunk_020
#print axioms array_faceLedger_chunk_021
#print axioms array_faceLedger_chunk_022_head
#print axioms array_faceLedger_chunk_022
#print axioms array_faceLedger_chunk_023_head
#print axioms array_faceLedger_chunk_023
#print axioms array_faceLedger_block_005
#print axioms geometryChars00_faceLedger_block_005_prefix
#print axioms geometryChars00_faceLedger_block_005_split
#print axioms array_faceLedger_original_block_005
#print axioms faceLedger_array_through_block_005

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
