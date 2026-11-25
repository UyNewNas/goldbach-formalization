import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00400

/-! Original vertex_values array block 5/6; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesChunk020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '8', '1', '6', '1', '/', '1', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '8', '1', '6', '1', '/', '1', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '4', '7', '/', '1', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '5', '8', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '6', '2', '1', '/', '2', '7', '2', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '3', '8', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk020Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['1', '0', '7', '8', '1', '6', '1', '/', '1', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '8', '1', '6', '1', '/', '1', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '4', '7', '/', '1', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '5', '8', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '6', '2', '1', '/', '2', '7', '2', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '9', '3', '8', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02100 : List SourceJson := vertexValuesChunk020Push00 vertexValuesArrayAcc02000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_020_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_020_prefix :
    (geometryChars00.drop 56667).take 477 = vertexValuesChunk020Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_020_split :
    geometryChars00.drop 56667 = vertexValuesChunk020Chars00 ++ geometryChars00.drop 57144 := by
  calc
    geometryChars00.drop 56667 =
        (geometryChars00.drop 56667).take 477 ++ (geometryChars00.drop 56667).drop 477 :=
      (List.take_append_drop 477 (geometryChars00.drop 56667)).symm
    _ = vertexValuesChunk020Chars00 ++ (geometryChars00.drop 56667).drop 477 :=
      congrArg (fun p => p ++ (geometryChars00.drop 56667).drop 477) geometryChars00_vertexValues_chunk_020_prefix
    _ = vertexValuesChunk020Chars00 ++ geometryChars00.drop 57144 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43)
      (SourceJson.white (vertexValuesChunk020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail)
        (vertexValuesChunk020Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_020 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 43)
      (SourceJson.white (geometryChars00.drop 56667)) acc =
      SourceJson.array (fuel + 42)
        (SourceJson.white (geometryChars00.drop 57144)) (vertexValuesChunk020Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 43) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_020_split).trans
    (array_vertexValues_chunk_020 fuel (geometryChars00.drop 57144) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_020_complete"
  err.flush

noncomputable def vertexValuesChunk021Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '2', '5', '7', '/', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '2', '5', '7', '/', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '7', '9', '/', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '4', '9', '3', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '9', '7', '4', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '3', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk021Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['6', '7', '2', '5', '7', '/', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '2', '5', '7', '/', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '7', '9', '/', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '4', '9', '3', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '7', '4', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '8', '3', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02200 : List SourceJson := vertexValuesChunk021Push00 vertexValuesArrayAcc02100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_021_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_021_prefix :
    (geometryChars00.drop 57144).take 450 = vertexValuesChunk021Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_021_split :
    geometryChars00.drop 57144 = vertexValuesChunk021Chars00 ++ geometryChars00.drop 57594 := by
  calc
    geometryChars00.drop 57144 =
        (geometryChars00.drop 57144).take 450 ++ (geometryChars00.drop 57144).drop 450 :=
      (List.take_append_drop 450 (geometryChars00.drop 57144)).symm
    _ = vertexValuesChunk021Chars00 ++ (geometryChars00.drop 57144).drop 450 :=
      congrArg (fun p => p ++ (geometryChars00.drop 57144).drop 450) geometryChars00_vertexValues_chunk_021_prefix
    _ = vertexValuesChunk021Chars00 ++ geometryChars00.drop 57594 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (vertexValuesChunk021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail)
        (vertexValuesChunk021Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_021 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (geometryChars00.drop 57144)) acc =
      SourceJson.array (fuel + 41)
        (SourceJson.white (geometryChars00.drop 57594)) (vertexValuesChunk021Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 42) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_021_split).trans
    (array_vertexValues_chunk_021 fuel (geometryChars00.drop 57594) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_021_complete"
  err.flush

noncomputable def vertexValuesChunk022Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '3', '1', '5', '3', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '3', '1', '5', '3', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk022Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['5', '5', '3', '1', '5', '3', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '3', '1', '5', '3', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02300 : List SourceJson := vertexValuesChunk022Push00 vertexValuesArrayAcc02200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_022_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_022_prefix :
    (geometryChars00.drop 57594).take 470 = vertexValuesChunk022Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_022_split :
    geometryChars00.drop 57594 = vertexValuesChunk022Chars00 ++ geometryChars00.drop 58064 := by
  calc
    geometryChars00.drop 57594 =
        (geometryChars00.drop 57594).take 470 ++ (geometryChars00.drop 57594).drop 470 :=
      (List.take_append_drop 470 (geometryChars00.drop 57594)).symm
    _ = vertexValuesChunk022Chars00 ++ (geometryChars00.drop 57594).drop 470 :=
      congrArg (fun p => p ++ (geometryChars00.drop 57594).drop 470) geometryChars00_vertexValues_chunk_022_prefix
    _ = vertexValuesChunk022Chars00 ++ geometryChars00.drop 58064 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (vertexValuesChunk022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail)
        (vertexValuesChunk022Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_022 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (geometryChars00.drop 57594)) acc =
      SourceJson.array (fuel + 40)
        (SourceJson.white (geometryChars00.drop 58064)) (vertexValuesChunk022Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_022_split).trans
    (array_vertexValues_chunk_022 fuel (geometryChars00.drop 58064) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_022_complete"
  err.flush

noncomputable def vertexValuesChunk023Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '7', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '7', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk023Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['2', '7', '6', '5', '7', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '5', '7', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02400 : List SourceJson := vertexValuesChunk023Push00 vertexValuesArrayAcc02300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_023_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_023_prefix :
    (geometryChars00.drop 58064).take 476 = vertexValuesChunk023Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_023_split :
    geometryChars00.drop 58064 = vertexValuesChunk023Chars00 ++ geometryChars00.drop 58540 := by
  calc
    geometryChars00.drop 58064 =
        (geometryChars00.drop 58064).take 476 ++ (geometryChars00.drop 58064).drop 476 :=
      (List.take_append_drop 476 (geometryChars00.drop 58064)).symm
    _ = vertexValuesChunk023Chars00 ++ (geometryChars00.drop 58064).drop 476 :=
      congrArg (fun p => p ++ (geometryChars00.drop 58064).drop 476) geometryChars00_vertexValues_chunk_023_prefix
    _ = vertexValuesChunk023Chars00 ++ geometryChars00.drop 58540 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (vertexValuesChunk023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 39) (SourceJson.white tail)
        (vertexValuesChunk023Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_023 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (geometryChars00.drop 58064)) acc =
      SourceJson.array (fuel + 39)
        (SourceJson.white (geometryChars00.drop 58540)) (vertexValuesChunk023Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 40) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_023_split).trans
    (array_vertexValues_chunk_023 fuel (geometryChars00.drop 58540) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_023_complete"
  err.flush

theorem vertexValues_array_through_block_005 (fuel : Nat) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 39)
        (SourceJson.white (geometryChars00.drop 58540)) vertexValuesArrayAcc02400 := by
  calc
    SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 43)
        (SourceJson.white (geometryChars00.drop 56667)) vertexValuesArrayAcc02000 :=
      vertexValues_array_through_block_004 fuel
    _ =
      SourceJson.array (fuel + 42)
        (SourceJson.white (geometryChars00.drop 57144)) vertexValuesArrayAcc02100 :=
      array_vertexValues_original_chunk_020 fuel vertexValuesArrayAcc02000
    _ =
      SourceJson.array (fuel + 41)
        (SourceJson.white (geometryChars00.drop 57594)) vertexValuesArrayAcc02200 :=
      array_vertexValues_original_chunk_021 fuel vertexValuesArrayAcc02100
    _ =
      SourceJson.array (fuel + 40)
        (SourceJson.white (geometryChars00.drop 58064)) vertexValuesArrayAcc02300 :=
      array_vertexValues_original_chunk_022 fuel vertexValuesArrayAcc02200
    _ =
      SourceJson.array (fuel + 39)
        (SourceJson.white (geometryChars00.drop 58540)) vertexValuesArrayAcc02400 :=
      array_vertexValues_original_chunk_023 fuel vertexValuesArrayAcc02300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_block_005_complete"
  err.flush

#print axioms geometryChars00_vertexValues_chunk_020_prefix
#print axioms geometryChars00_vertexValues_chunk_020_split
#print axioms array_vertexValues_chunk_020
#print axioms array_vertexValues_original_chunk_020
#print axioms geometryChars00_vertexValues_chunk_021_prefix
#print axioms geometryChars00_vertexValues_chunk_021_split
#print axioms array_vertexValues_chunk_021
#print axioms array_vertexValues_original_chunk_021
#print axioms geometryChars00_vertexValues_chunk_022_prefix
#print axioms geometryChars00_vertexValues_chunk_022_split
#print axioms array_vertexValues_chunk_022
#print axioms array_vertexValues_original_chunk_022
#print axioms geometryChars00_vertexValues_chunk_023_prefix
#print axioms geometryChars00_vertexValues_chunk_023_split
#print axioms array_vertexValues_chunk_023
#print axioms array_vertexValues_original_chunk_023
#print axioms vertexValues_array_through_block_005

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
