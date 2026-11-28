import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! Original vertex_values grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VertexValuesBlock004

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_before_reader"
  err.flush

noncomputable def chunk0032Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def chunk0032Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])])]) :: (acc)

theorem array_chunk0032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0032Push00 acc).reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0032Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0032Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0032Chars00 ++ (tail) := by simp only [blockChars]
  calc
    SourceJson.array (fuel + 37) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 37) (SourceJson.white (chunk0032Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 37) (SourceJson.white chars) acc) hinput
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0032 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 63467).take 471 = blockChars := by rfl

theorem block_original_split : sourceRest 63467 = blockChars ++ sourceRest 63938 := by
  calc
    sourceRest 63467 = (sourceRest 63467).take 471 ++ (sourceRest 63467).drop 471 :=
      (List.take_append_drop 471 (sourceRest 63467)).symm
    _ = blockChars ++ (sourceRest 63467).drop 471 :=
      congrArg (fun part => part ++ (sourceRest 63467).drop 471) block_original_prefix
    _ = blockChars ++ sourceRest 63938 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 63467 471)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (sourceRest 63467)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 63938) :=
  (congrArg (fun chars => SourceJson.array (fuel + 37) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 63938) acc)

#print axioms array_chunk0032
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end VertexValuesBlock004

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
