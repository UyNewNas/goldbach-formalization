import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original all_original_constraint_minima grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace AllOriginalConstraintMinimaBlock006

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_before_reader"
  err.flush

noncomputable def chunk0048Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '7', '0', '8', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ']']
noncomputable def chunk0048Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '6', '5', '4', '7', '0', '8', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: (acc)

theorem array_chunk0048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0048Push00 acc).reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0048Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0048Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0048Chars00 ++ (tail) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 20) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 20) (SourceJson.white (chunk0048Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 20) (SourceJson.white chars) acc) hinput
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0048 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 62996).take 30 = blockChars := by rfl

theorem block_original_split : sourceRest 62996 = blockChars ++ sourceRest 63026 := by
  calc
    sourceRest 62996 = (sourceRest 62996).take 30 ++ (sourceRest 62996).drop 30 :=
      (List.take_append_drop 30 (sourceRest 62996)).symm
    _ = blockChars ++ (sourceRest 62996).drop 30 :=
      congrArg (fun part => part ++ (sourceRest 62996).drop 30) block_original_prefix
    _ = blockChars ++ sourceRest 63026 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 62996 30)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (sourceRest 62996)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 63026) :=
  (congrArg (fun chars => SourceJson.array (fuel + 20) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 63026) acc)

#print axioms array_chunk0048
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock006

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
