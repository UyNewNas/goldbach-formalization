import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! Original vertices grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace VerticesBlock002

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ']']
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) :: (acc)

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0016Push00 acc).reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0016Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0016Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0016Chars00 ++ (tail) := by simp only [blockChars]
  calc
    SourceJson.array (fuel + 28) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 28) (SourceJson.white (chunk0016Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 28) (SourceJson.white chars) acc) hinput
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0016 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 48119).take 221 = blockChars := by rfl

theorem block_original_split : sourceRest 48119 = blockChars ++ sourceRest 48340 := by
  calc
    sourceRest 48119 = (sourceRest 48119).take 221 ++ (sourceRest 48119).drop 221 :=
      (List.take_append_drop 221 (sourceRest 48119)).symm
    _ = blockChars ++ (sourceRest 48119).drop 221 :=
      congrArg (fun part => part ++ (sourceRest 48119).drop 221) block_original_prefix
    _ = blockChars ++ sourceRest 48340 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 48119 221)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (sourceRest 48119)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 48340) :=
  (congrArg (fun chars => SourceJson.array (fuel + 28) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 48340) acc)

#print axioms array_chunk0016
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end VerticesBlock002

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
