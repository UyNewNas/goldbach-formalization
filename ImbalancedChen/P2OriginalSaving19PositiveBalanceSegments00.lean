import ImbalancedChen.P2OriginalSaving19FirstThreeFields00

/-!
Generated fourth-field pilot on exact raw CRLF bytes. The 11-item array is
proved by small original-reader transitions, and its theorem is composed into
the original object continuation. Accumulators stay in the reader's reverse
order. The full unconsumed suffix is always an arbitrary tail or a drop of the
accepted geometryChars00; it is never copied into the generated proof.
Host token/AST/fuel planning is untrusted. The theorems below are its checks.
-/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def positiveBalanceHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '_', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'b', 'a', 'l', 'a', 'n', 'c', 'e', '"', ':', ' ']
def positiveBalanceChunk0Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '9', '/', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',']
def positiveBalanceChunk1Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '/', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '/', '3', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '/', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '7', '/', '3', '9', '"', ',']
def positiveBalanceChunk2Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '/', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '2', '/', '1', '3', '"', '\r', '\n', ' ', ' ', ']']
def positiveBalanceArrayChars00 : List Char := '[' :: (positiveBalanceChunk0Chars00 ++ positiveBalanceChunk1Chars00 ++ positiveBalanceChunk2Chars00)
def positiveBalancePrefixChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '_', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'b', 'a', 'l', 'a', 'n', 'c', 'e', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '9', '/', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '/', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '/', '3', '1', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '/', '2', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '7', '/', '3', '9', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '/', '1', '3', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '2', '/', '1', '3', '"', '\r', '\n', ' ', ' ', ']', ',']
def positiveBalanceKey00 : String := String.ofList ['p', 'o', 's', 'i', 't', 'i', 'v', 'e', '_', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'b', 'a', 'l', 'a', 'n', 'c', 'e']
def positiveBalanceItems00 : List SourceJson := [
    .str (String.ofList ['1']),
    .str (String.ofList ['1']),
    .str (String.ofList ['1', '9', '/', '2', '6']),
    .str (String.ofList ['1']),
    .str (String.ofList ['1', '7', '6', '/', '3', '9']),
    .str (String.ofList ['3', '8', '5', '/', '3', '1', '2']),
    .str (String.ofList ['7', '/', '2', '6']),
    .str (String.ofList ['1', '7', '/', '3', '9']),
    .str (String.ofList ['1', '1', '/', '1', '3']),
    .str (String.ofList ['5', '/', '1', '3']),
    .str (String.ofList ['2', '2', '/', '1', '3'])
  ]
def positiveBalanceValue00 : SourceJson := .arr positiveBalanceItems00
def positiveBalanceAcc00 : List (String × SourceJson) :=
  (positiveBalanceKey00, positiveBalanceValue00) :: facetIndicesAcc00

def positiveBalanceArrayAcc000 : List SourceJson := []
def positiveBalanceArrayAcc100 : List SourceJson := [.str (String.ofList ['1']), .str (String.ofList ['1', '9', '/', '2', '6']), .str (String.ofList ['1']), .str (String.ofList ['1'])]
def positiveBalanceArrayAcc200 : List SourceJson := [.str (String.ofList ['1', '7', '/', '3', '9']), .str (String.ofList ['7', '/', '2', '6']), .str (String.ofList ['3', '8', '5', '/', '3', '1', '2']), .str (String.ofList ['1', '7', '6', '/', '3', '9']), .str (String.ofList ['1']), .str (String.ofList ['1', '9', '/', '2', '6']), .str (String.ofList ['1']), .str (String.ofList ['1'])]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE before_raw_bindings"
  err.flush

theorem geometryChars00_positive_balance_prefix :
    (geometryChars00.drop 179).take 180 = positiveBalancePrefixChars00 := by
  rfl

theorem positive_balance_prefix_decomposition :
    positiveBalancePrefixChars00 =
      positiveBalanceHeaderChars00 ++ positiveBalanceArrayChars00 ++ [','] := by
  rfl

theorem geometryChars00_positive_balance_split :
    geometryChars00.drop 179 = positiveBalancePrefixChars00 ++ geometryChars00.drop 359 := by
  calc
    geometryChars00.drop 179 =
        (geometryChars00.drop 179).take 180 ++ (geometryChars00.drop 179).drop 180 :=
      (List.take_append_drop 180 (geometryChars00.drop 179)).symm
    _ = positiveBalancePrefixChars00 ++ (geometryChars00.drop 179).drop 180 :=
      congrArg (fun p => p ++ (geometryChars00.drop 179).drop 180)
        geometryChars00_positive_balance_prefix
    _ = positiveBalancePrefixChars00 ++ geometryChars00.drop 359 := by
      rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE after_raw_bindings"
  err.flush

/-- Original array reader; item interval [0, 4] and raw span [211, 255].
The fixed prefix ends in ','; the arbitrary tail is not inspected. -/
theorem array_positive_balance_chunk_0 (fuel : Nat) (tail : List Char) :
    SourceJson.array (fuel + 18)
      (SourceJson.white (positiveBalanceChunk0Chars00 ++ tail)) positiveBalanceArrayAcc000 =
      SourceJson.array (fuel + 14) (SourceJson.white tail)
        positiveBalanceArrayAcc100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE after_array_chunk_0"
  err.flush

/-- Original array reader; item interval [4, 8] and raw span [255, 313].
The fixed prefix ends in ','; the arbitrary tail is not inspected. -/
theorem array_positive_balance_chunk_1 (fuel : Nat) (tail : List Char) :
    SourceJson.array (fuel + 14)
      (SourceJson.white (positiveBalanceChunk1Chars00 ++ tail)) positiveBalanceArrayAcc100 =
      SourceJson.array (fuel + 10) (SourceJson.white tail)
        positiveBalanceArrayAcc200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE after_array_chunk_1"
  err.flush

/-- Original array reader; item interval [8, 11] and raw span [313, 358].
The fixed prefix ends in ']'; the arbitrary tail is not inspected. -/
theorem array_positive_balance_chunk_2 (fuel : Nat) (tail : List Char) :
    SourceJson.array (fuel + 10)
      (SourceJson.white (positiveBalanceChunk2Chars00 ++ tail)) positiveBalanceArrayAcc200 =
      .ok (positiveBalanceValue00, tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE after_array_chunk_2"
  err.flush

/-- Composition of the opaque original-array transition theorems. -/
theorem value_positive_balance_array (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (positiveBalanceArrayChars00 ++ tail) =
      .ok (positiveBalanceValue00, tail) := by
  have hinput : positiveBalanceArrayChars00 ++ tail = '[' :: (positiveBalanceChunk0Chars00 ++ (positiveBalanceChunk1Chars00 ++ (positiveBalanceChunk2Chars00 ++ (tail)))) := by
    simp only [positiveBalanceArrayChars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (positiveBalanceArrayChars00 ++ tail) =
        SourceJson.value (fuel + 19) ('[' :: (positiveBalanceChunk0Chars00 ++ (positiveBalanceChunk1Chars00 ++ (positiveBalanceChunk2Chars00 ++ (tail))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.array (fuel + 18) (SourceJson.white (positiveBalanceChunk0Chars00 ++ (positiveBalanceChunk1Chars00 ++ (positiveBalanceChunk2Chars00 ++ (tail)))))
        positiveBalanceArrayAcc000 := by rfl
    _ = SourceJson.array (fuel + 14)
        (SourceJson.white (positiveBalanceChunk1Chars00 ++ (positiveBalanceChunk2Chars00 ++ (tail)))) positiveBalanceArrayAcc100 :=
      array_positive_balance_chunk_0 fuel (positiveBalanceChunk1Chars00 ++ (positiveBalanceChunk2Chars00 ++ (tail)))
    _ = SourceJson.array (fuel + 10)
        (SourceJson.white (positiveBalanceChunk2Chars00 ++ (tail))) positiveBalanceArrayAcc200 :=
      array_positive_balance_chunk_1 fuel (positiveBalanceChunk2Chars00 ++ (tail))
    _ = .ok (positiveBalanceValue00, tail) :=
      array_positive_balance_chunk_2 fuel tail

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE after_array_composition"
  err.flush

/-- The original post-value continuation. The header theorem below
reduces the original duplicate-key test against all three accepted prior keys. -/
def positiveBalanceAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((positiveBalanceKey00, result.1) :: facetIndicesAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((positiveBalanceKey00, result.1) :: facetIndicesAcc00)
  | _ => .error "object separator missing"

theorem object_positive_balance_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (positiveBalanceHeaderChars00 ++ rest))
      facetIndicesAcc00 =
      (SourceJson.value (fuel + 24) rest).bind
        (positiveBalanceAfterValue00 (fuel + 24)) := by
  rfl

theorem object_positive_balance_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (positiveBalancePrefixChars00 ++ tail))
      facetIndicesAcc00 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) positiveBalanceAcc00 := by
  have hinput : positiveBalancePrefixChars00 ++ tail =
      positiveBalanceHeaderChars00 ++ (positiveBalanceArrayChars00 ++ (',' :: tail)) := by
    rw [positive_balance_prefix_decomposition]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  calc
    SourceJson.object (fuel + 25) (SourceJson.white (positiveBalancePrefixChars00 ++ tail))
        facetIndicesAcc00 =
      SourceJson.object (fuel + 25)
        (SourceJson.white (positiveBalanceHeaderChars00 ++ (positiveBalanceArrayChars00 ++ (',' :: tail))))
        facetIndicesAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 25) (SourceJson.white s) facetIndicesAcc00)
        hinput
    _ = (SourceJson.value (fuel + 24) (positiveBalanceArrayChars00 ++ (',' :: tail))).bind
        (positiveBalanceAfterValue00 (fuel + 24)) :=
      object_positive_balance_header fuel (positiveBalanceArrayChars00 ++ (',' :: tail))
    _ = (Except.ok (positiveBalanceValue00, ',' :: tail)).bind
        (positiveBalanceAfterValue00 (fuel + 24)) :=
      congrArg (fun r => r.bind (positiveBalanceAfterValue00 (fuel + 24)))
        (value_positive_balance_array (fuel + 5) (',' :: tail))
    _ = SourceJson.object (fuel + 24) (SourceJson.white tail) positiveBalanceAcc00 := by
      rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE after_object_composition"
  err.flush

theorem geometryChars00_positive_balance_step :
    SourceJson.object 195131 (SourceJson.white (geometryChars00.drop 179)) facetIndicesAcc00 =
      SourceJson.object 195130 (SourceJson.white (geometryChars00.drop 359)) positiveBalanceAcc00 := by
  exact (congrArg (fun s => SourceJson.object 195131 (SourceJson.white s) facetIndicesAcc00)
      geometryChars00_positive_balance_split).trans
    (object_positive_balance_prefix 195106 (geometryChars00.drop 359))

/-- Exact four-field transition on the complete original character input.
The remaining object parse is retained, not assumed or claimed successful. -/
theorem geometryChars00_through_positive_balance :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195130 (SourceJson.white (geometryChars00.drop 359)) positiveBalanceAcc00 := by
  exact geometryChars00_through_facet_indices.trans geometryChars00_positive_balance_step

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_POSITIVE_BALANCE after_closed_original_reader_step"
  err.flush

#print axioms geometryChars00_positive_balance_prefix
#print axioms positive_balance_prefix_decomposition
#print axioms geometryChars00_positive_balance_split
#print axioms array_positive_balance_chunk_0
#print axioms array_positive_balance_chunk_1
#print axioms array_positive_balance_chunk_2
#print axioms value_positive_balance_array
#print axioms object_positive_balance_header
#print axioms object_positive_balance_prefix
#print axioms geometryChars00_positive_balance_step
#print axioms geometryChars00_through_positive_balance

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
