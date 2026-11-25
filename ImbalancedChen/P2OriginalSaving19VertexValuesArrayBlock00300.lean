import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00200

/-! Original vertex_values array block 3/6; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesChunk012Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '1', '2', '5', '9', '5', '3', '0', '8', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '1', '2', '5', '9', '5', '3', '0', '8', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '1', '2', '5', '9', '5', '3', '0', '8', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '9', '2', '9', '/', '8', '2', '8', '1', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '0', '3', '2', '4', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '6', '1', '3', '/', '4', '2', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '6', '8', '7', '1', '/', '1', '0', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '5', '3', '1', '3', '7', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '5', '3', '0', '4', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '1', '0', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '6', '8', '7', '1', '/', '4', '2', '4', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk012Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['1', '2', '5', '9', '5', '3', '0', '8', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['1', '2', '5', '9', '5', '3', '0', '8', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['1', '2', '5', '9', '5', '3', '0', '8', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['2', '9', '2', '9', '/', '8', '2', '8', '1', '2', '5'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['1', '8', '7', '0', '3', '2', '4', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '6', '1', '3', '/', '4', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '6', '8', '7', '1', '/', '1', '0', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '5', '3', '1', '3', '7', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '9', '5', '3', '0', '4', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '1', '0', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '6', '8', '7', '1', '/', '4', '2', '4', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01300 : List SourceJson := vertexValuesChunk012Push00 vertexValuesArrayAcc01200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_012_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_012_prefix :
    (geometryChars00.drop 52821).take 512 = vertexValuesChunk012Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_012_split :
    geometryChars00.drop 52821 = vertexValuesChunk012Chars00 ++ geometryChars00.drop 53333 := by
  calc
    geometryChars00.drop 52821 =
        (geometryChars00.drop 52821).take 512 ++ (geometryChars00.drop 52821).drop 512 :=
      (List.take_append_drop 512 (geometryChars00.drop 52821)).symm
    _ = vertexValuesChunk012Chars00 ++ (geometryChars00.drop 52821).drop 512 :=
      congrArg (fun p => p ++ (geometryChars00.drop 52821).drop 512) geometryChars00_vertexValues_chunk_012_prefix
    _ = vertexValuesChunk012Chars00 ++ geometryChars00.drop 53333 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51)
      (SourceJson.white (vertexValuesChunk012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail)
        (vertexValuesChunk012Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_012 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 51)
      (SourceJson.white (geometryChars00.drop 52821)) acc =
      SourceJson.array (fuel + 50)
        (SourceJson.white (geometryChars00.drop 53333)) (vertexValuesChunk012Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 51) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_012_split).trans
    (array_vertexValues_chunk_012 fuel (geometryChars00.drop 53333) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_012_complete"
  err.flush

noncomputable def vertexValuesChunk013Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '1', '4', '0', '2', '9', '6', '8', '3', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '1', '4', '0', '2', '9', '6', '8', '3', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '1', '4', '0', '2', '9', '6', '8', '3', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '7', '4', '9', '/', '1', '1', '8', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '0', '9', '4', '0', '3', '/', '4', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '5', '9', '3', '6', '3', '/', '4', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '2', '1', '/', '1', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '9', '6', '8', '8', '7', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '9', '6', '7', '9', '1', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '5', '6', '2', '9', '/', '1', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk013Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['1', '4', '0', '2', '9', '6', '8', '3', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['1', '4', '0', '2', '9', '6', '8', '3', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['1', '4', '0', '2', '9', '6', '8', '3', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['3', '7', '4', '9', '/', '1', '1', '8', '0', '0', '0', '0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['4', '2', '0', '9', '4', '0', '3', '/', '4', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '5', '9', '3', '6', '3', '/', '4', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '3', '1', '2', '1', '/', '1', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '9', '6', '8', '8', '7', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '9', '6', '7', '9', '1', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '5', '6', '2', '9', '/', '1', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01400 : List SourceJson := vertexValuesChunk013Push00 vertexValuesArrayAcc01300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_013_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_013_prefix :
    (geometryChars00.drop 53333).take 510 = vertexValuesChunk013Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_013_split :
    geometryChars00.drop 53333 = vertexValuesChunk013Chars00 ++ geometryChars00.drop 53843 := by
  calc
    geometryChars00.drop 53333 =
        (geometryChars00.drop 53333).take 510 ++ (geometryChars00.drop 53333).drop 510 :=
      (List.take_append_drop 510 (geometryChars00.drop 53333)).symm
    _ = vertexValuesChunk013Chars00 ++ (geometryChars00.drop 53333).drop 510 :=
      congrArg (fun p => p ++ (geometryChars00.drop 53333).drop 510) geometryChars00_vertexValues_chunk_013_prefix
    _ = vertexValuesChunk013Chars00 ++ geometryChars00.drop 53843 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (vertexValuesChunk013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail)
        (vertexValuesChunk013Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_013 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (geometryChars00.drop 53333)) acc =
      SourceJson.array (fuel + 49)
        (SourceJson.white (geometryChars00.drop 53843)) (vertexValuesChunk013Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 50) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_013_split).trans
    (array_vertexValues_chunk_013 fuel (geometryChars00.drop 53843) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_013_complete"
  err.flush

noncomputable def vertexValuesChunk014Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '7', '8', '5', '9', '4', '5', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '1', '9', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '3', '1', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '6', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk014Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '7', '8', '5', '9', '4', '5', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '5', '1', '9', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '1', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '6', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01500 : List SourceJson := vertexValuesChunk014Push00 vertexValuesArrayAcc01400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_014_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_014_prefix :
    (geometryChars00.drop 53843).take 467 = vertexValuesChunk014Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_014_split :
    geometryChars00.drop 53843 = vertexValuesChunk014Chars00 ++ geometryChars00.drop 54310 := by
  calc
    geometryChars00.drop 53843 =
        (geometryChars00.drop 53843).take 467 ++ (geometryChars00.drop 53843).drop 467 :=
      (List.take_append_drop 467 (geometryChars00.drop 53843)).symm
    _ = vertexValuesChunk014Chars00 ++ (geometryChars00.drop 53843).drop 467 :=
      congrArg (fun p => p ++ (geometryChars00.drop 53843).drop 467) geometryChars00_vertexValues_chunk_014_prefix
    _ = vertexValuesChunk014Chars00 ++ geometryChars00.drop 54310 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (vertexValuesChunk014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail)
        (vertexValuesChunk014Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_014 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (geometryChars00.drop 53843)) acc =
      SourceJson.array (fuel + 48)
        (SourceJson.white (geometryChars00.drop 54310)) (vertexValuesChunk014Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_014_split).trans
    (array_vertexValues_chunk_014 fuel (geometryChars00.drop 54310) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_014_complete"
  err.flush

noncomputable def vertexValuesChunk015Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '8', '3', '5', '7', '8', '3', '6', '1', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk015Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['8', '3', '5', '7', '8', '3', '6', '1', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01600 : List SourceJson := vertexValuesChunk015Push00 vertexValuesArrayAcc01500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_015_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_015_prefix :
    (geometryChars00.drop 54310).take 478 = vertexValuesChunk015Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_015_split :
    geometryChars00.drop 54310 = vertexValuesChunk015Chars00 ++ geometryChars00.drop 54788 := by
  calc
    geometryChars00.drop 54310 =
        (geometryChars00.drop 54310).take 478 ++ (geometryChars00.drop 54310).drop 478 :=
      (List.take_append_drop 478 (geometryChars00.drop 54310)).symm
    _ = vertexValuesChunk015Chars00 ++ (geometryChars00.drop 54310).drop 478 :=
      congrArg (fun p => p ++ (geometryChars00.drop 54310).drop 478) geometryChars00_vertexValues_chunk_015_prefix
    _ = vertexValuesChunk015Chars00 ++ geometryChars00.drop 54788 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (vertexValuesChunk015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail)
        (vertexValuesChunk015Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_015 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (geometryChars00.drop 54310)) acc =
      SourceJson.array (fuel + 47)
        (SourceJson.white (geometryChars00.drop 54788)) (vertexValuesChunk015Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 48) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_015_split).trans
    (array_vertexValues_chunk_015 fuel (geometryChars00.drop 54788) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_015_complete"
  err.flush

theorem vertexValues_array_through_block_003 (fuel : Nat) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 47)
        (SourceJson.white (geometryChars00.drop 54788)) vertexValuesArrayAcc01600 := by
  calc
    SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 51)
        (SourceJson.white (geometryChars00.drop 52821)) vertexValuesArrayAcc01200 :=
      vertexValues_array_through_block_002 fuel
    _ =
      SourceJson.array (fuel + 50)
        (SourceJson.white (geometryChars00.drop 53333)) vertexValuesArrayAcc01300 :=
      array_vertexValues_original_chunk_012 fuel vertexValuesArrayAcc01200
    _ =
      SourceJson.array (fuel + 49)
        (SourceJson.white (geometryChars00.drop 53843)) vertexValuesArrayAcc01400 :=
      array_vertexValues_original_chunk_013 fuel vertexValuesArrayAcc01300
    _ =
      SourceJson.array (fuel + 48)
        (SourceJson.white (geometryChars00.drop 54310)) vertexValuesArrayAcc01500 :=
      array_vertexValues_original_chunk_014 fuel vertexValuesArrayAcc01400
    _ =
      SourceJson.array (fuel + 47)
        (SourceJson.white (geometryChars00.drop 54788)) vertexValuesArrayAcc01600 :=
      array_vertexValues_original_chunk_015 fuel vertexValuesArrayAcc01500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_block_003_complete"
  err.flush

#print axioms geometryChars00_vertexValues_chunk_012_prefix
#print axioms geometryChars00_vertexValues_chunk_012_split
#print axioms array_vertexValues_chunk_012
#print axioms array_vertexValues_original_chunk_012
#print axioms geometryChars00_vertexValues_chunk_013_prefix
#print axioms geometryChars00_vertexValues_chunk_013_split
#print axioms array_vertexValues_chunk_013
#print axioms array_vertexValues_original_chunk_013
#print axioms geometryChars00_vertexValues_chunk_014_prefix
#print axioms geometryChars00_vertexValues_chunk_014_split
#print axioms array_vertexValues_chunk_014
#print axioms array_vertexValues_original_chunk_014
#print axioms geometryChars00_vertexValues_chunk_015_prefix
#print axioms geometryChars00_vertexValues_chunk_015_split
#print axioms array_vertexValues_chunk_015
#print axioms array_vertexValues_original_chunk_015
#print axioms vertexValues_array_through_block_003

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
