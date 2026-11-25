import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00000

/-! Original vertex_values array block 1/6; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesChunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '3', '1', '1', '2', '4', '9', '7', '/', '5', '2', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '3', '1', '1', '2', '4', '9', '7', '/', '5', '2', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '1', '2', '1', '7', '0', '3', '3', '8', '1', '/', '2', '0', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '3', '1', '1', '2', '4', '9', '7', '/', '5', '2', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '3', '1', '2', '2', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '3', '1', '2', '2', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '0', '9', '3', '7', '1', '/', '5', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '4', '0', '1', '/', '1', '3', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '2', '8', '1', '7', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '5', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '3', '7', '4', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['3', '1', '1', '2', '4', '9', '7', '/', '5', '2', '2', '5', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['3', '1', '1', '2', '4', '9', '7', '/', '5', '2', '2', '5', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['1', '2', '1', '7', '0', '3', '3', '8', '1', '/', '2', '0', '9', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['3', '1', '1', '2', '4', '9', '7', '/', '5', '2', '2', '5', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['1', '0', '0', '3', '1', '2', '2', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '3', '1', '2', '2', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '0', '9', '3', '7', '1', '/', '5', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '4', '0', '1', '/', '1', '3', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['8', '3', '2', '8', '1', '7', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '5', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '3', '7', '4', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00500 : List SourceJson := vertexValuesChunk004Push00 vertexValuesArrayAcc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_004_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_004_prefix :
    (geometryChars00.drop 48972).take 493 = vertexValuesChunk004Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_004_split :
    geometryChars00.drop 48972 = vertexValuesChunk004Chars00 ++ geometryChars00.drop 49465 := by
  calc
    geometryChars00.drop 48972 =
        (geometryChars00.drop 48972).take 493 ++ (geometryChars00.drop 48972).drop 493 :=
      (List.take_append_drop 493 (geometryChars00.drop 48972)).symm
    _ = vertexValuesChunk004Chars00 ++ (geometryChars00.drop 48972).drop 493 :=
      congrArg (fun p => p ++ (geometryChars00.drop 48972).drop 493) geometryChars00_vertexValues_chunk_004_prefix
    _ = vertexValuesChunk004Chars00 ++ geometryChars00.drop 49465 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59)
      (SourceJson.white (vertexValuesChunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail)
        (vertexValuesChunk004Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_004 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 59)
      (SourceJson.white (geometryChars00.drop 48972)) acc =
      SourceJson.array (fuel + 58)
        (SourceJson.white (geometryChars00.drop 49465)) (vertexValuesChunk004Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 59) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_004_split).trans
    (array_vertexValues_chunk_004 fuel (geometryChars00.drop 49465) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_004_complete"
  err.flush

noncomputable def vertexValuesChunk005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '4', '9', '4', '6', '8', '7', '/', '8', '3', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '4', '9', '4', '6', '8', '7', '/', '8', '3', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '8', '9', '6', '5', '6', '8', '9', '/', '4', '9', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '4', '9', '4', '6', '8', '7', '/', '8', '3', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '4', '9', '7', '9', '/', '4', '1', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '4', '9', '7', '9', '/', '4', '1', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '6', '2', '4', '9', '/', '1', '2', '4', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '2', '3', '6', '/', '7', '7', '8', '1', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '9', '3', '7', '9', '/', '8', '3', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '3', '6', '1', '/', '1', '2', '4', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk005Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['4', '9', '4', '6', '8', '7', '/', '8', '3', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['4', '9', '4', '6', '8', '7', '/', '8', '3', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '8', '9', '6', '5', '6', '8', '9', '/', '4', '9', '8', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['4', '9', '4', '6', '8', '7', '/', '8', '3', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['4', '1', '2', '4', '9', '7', '9', '/', '4', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '2', '4', '9', '7', '9', '/', '4', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '6', '2', '4', '9', '/', '1', '2', '4', '5', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '2', '3', '6', '/', '7', '7', '8', '1', '2', '5']), .str (String.ofList ['6', '5', '9', '3', '7', '9', '/', '8', '3', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '4', '3', '6', '1', '/', '1', '2', '4', '5', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00600 : List SourceJson := vertexValuesChunk005Push00 vertexValuesArrayAcc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_005_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_005_prefix :
    (geometryChars00.drop 49465).take 467 = vertexValuesChunk005Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_005_split :
    geometryChars00.drop 49465 = vertexValuesChunk005Chars00 ++ geometryChars00.drop 49932 := by
  calc
    geometryChars00.drop 49465 =
        (geometryChars00.drop 49465).take 467 ++ (geometryChars00.drop 49465).drop 467 :=
      (List.take_append_drop 467 (geometryChars00.drop 49465)).symm
    _ = vertexValuesChunk005Chars00 ++ (geometryChars00.drop 49465).drop 467 :=
      congrArg (fun p => p ++ (geometryChars00.drop 49465).drop 467) geometryChars00_vertexValues_chunk_005_prefix
    _ = vertexValuesChunk005Chars00 ++ geometryChars00.drop 49932 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58)
      (SourceJson.white (vertexValuesChunk005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail)
        (vertexValuesChunk005Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_005 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 58)
      (SourceJson.white (geometryChars00.drop 49465)) acc =
      SourceJson.array (fuel + 57)
        (SourceJson.white (geometryChars00.drop 49932)) (vertexValuesChunk005Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 58) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_005_split).trans
    (array_vertexValues_chunk_005 fuel (geometryChars00.drop 49932) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_005_complete"
  err.flush

noncomputable def vertexValuesChunk006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '8', '6', '7', '1', '9', '0', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '6', '9', '1', '1', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '6', '9', '1', '1', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk006Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['8', '6', '7', '1', '9', '0', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['1', '7', '9', '6', '9', '1', '1', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '6', '9', '1', '1', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00700 : List SourceJson := vertexValuesChunk006Push00 vertexValuesArrayAcc00600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_006_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_006_prefix :
    (geometryChars00.drop 49932).take 477 = vertexValuesChunk006Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_006_split :
    geometryChars00.drop 49932 = vertexValuesChunk006Chars00 ++ geometryChars00.drop 50409 := by
  calc
    geometryChars00.drop 49932 =
        (geometryChars00.drop 49932).take 477 ++ (geometryChars00.drop 49932).drop 477 :=
      (List.take_append_drop 477 (geometryChars00.drop 49932)).symm
    _ = vertexValuesChunk006Chars00 ++ (geometryChars00.drop 49932).drop 477 :=
      congrArg (fun p => p ++ (geometryChars00.drop 49932).drop 477) geometryChars00_vertexValues_chunk_006_prefix
    _ = vertexValuesChunk006Chars00 ++ geometryChars00.drop 50409 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57)
      (SourceJson.white (vertexValuesChunk006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 56) (SourceJson.white tail)
        (vertexValuesChunk006Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_006 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 57)
      (SourceJson.white (geometryChars00.drop 49932)) acc =
      SourceJson.array (fuel + 56)
        (SourceJson.white (geometryChars00.drop 50409)) (vertexValuesChunk006Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 57) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_006_split).trans
    (array_vertexValues_chunk_006 fuel (geometryChars00.drop 50409) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_006_complete"
  err.flush

noncomputable def vertexValuesChunk007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '8', '6', '7', '1', '9', '0', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk007Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['8', '6', '7', '1', '9', '0', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00800 : List SourceJson := vertexValuesChunk007Push00 vertexValuesArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_007_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_007_prefix :
    (geometryChars00.drop 50409).take 478 = vertexValuesChunk007Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_007_split :
    geometryChars00.drop 50409 = vertexValuesChunk007Chars00 ++ geometryChars00.drop 50887 := by
  calc
    geometryChars00.drop 50409 =
        (geometryChars00.drop 50409).take 478 ++ (geometryChars00.drop 50409).drop 478 :=
      (List.take_append_drop 478 (geometryChars00.drop 50409)).symm
    _ = vertexValuesChunk007Chars00 ++ (geometryChars00.drop 50409).drop 478 :=
      congrArg (fun p => p ++ (geometryChars00.drop 50409).drop 478) geometryChars00_vertexValues_chunk_007_prefix
    _ = vertexValuesChunk007Chars00 ++ geometryChars00.drop 50887 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 56)
      (SourceJson.white (vertexValuesChunk007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white tail)
        (vertexValuesChunk007Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_007 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 56)
      (SourceJson.white (geometryChars00.drop 50409)) acc =
      SourceJson.array (fuel + 55)
        (SourceJson.white (geometryChars00.drop 50887)) (vertexValuesChunk007Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 56) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_007_split).trans
    (array_vertexValues_chunk_007 fuel (geometryChars00.drop 50887) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_007_complete"
  err.flush

theorem vertexValues_array_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 55)
        (SourceJson.white (geometryChars00.drop 50887)) vertexValuesArrayAcc00800 := by
  calc
    SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 59)
        (SourceJson.white (geometryChars00.drop 48972)) vertexValuesArrayAcc00400 :=
      vertexValues_array_through_block_000 fuel
    _ =
      SourceJson.array (fuel + 58)
        (SourceJson.white (geometryChars00.drop 49465)) vertexValuesArrayAcc00500 :=
      array_vertexValues_original_chunk_004 fuel vertexValuesArrayAcc00400
    _ =
      SourceJson.array (fuel + 57)
        (SourceJson.white (geometryChars00.drop 49932)) vertexValuesArrayAcc00600 :=
      array_vertexValues_original_chunk_005 fuel vertexValuesArrayAcc00500
    _ =
      SourceJson.array (fuel + 56)
        (SourceJson.white (geometryChars00.drop 50409)) vertexValuesArrayAcc00700 :=
      array_vertexValues_original_chunk_006 fuel vertexValuesArrayAcc00600
    _ =
      SourceJson.array (fuel + 55)
        (SourceJson.white (geometryChars00.drop 50887)) vertexValuesArrayAcc00800 :=
      array_vertexValues_original_chunk_007 fuel vertexValuesArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_block_001_complete"
  err.flush

#print axioms geometryChars00_vertexValues_chunk_004_prefix
#print axioms geometryChars00_vertexValues_chunk_004_split
#print axioms array_vertexValues_chunk_004
#print axioms array_vertexValues_original_chunk_004
#print axioms geometryChars00_vertexValues_chunk_005_prefix
#print axioms geometryChars00_vertexValues_chunk_005_split
#print axioms array_vertexValues_chunk_005
#print axioms array_vertexValues_original_chunk_005
#print axioms geometryChars00_vertexValues_chunk_006_prefix
#print axioms geometryChars00_vertexValues_chunk_006_split
#print axioms array_vertexValues_chunk_006
#print axioms array_vertexValues_original_chunk_006
#print axioms geometryChars00_vertexValues_chunk_007_prefix
#print axioms geometryChars00_vertexValues_chunk_007_split
#print axioms array_vertexValues_chunk_007
#print axioms array_vertexValues_original_chunk_007
#print axioms vertexValues_array_through_block_001

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
