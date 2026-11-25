import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Original all_original_constraint_minima grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
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

noncomputable def chunk0048Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '6', '9', '2', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ']']
noncomputable def chunk0048Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '6', '5', '4', '6', '9', '2', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: (acc)

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
    (sourceRest 152962).take 30 = blockChars := by rfl

theorem block_original_split : sourceRest 152962 = blockChars ++ sourceRest 152992 := by
  calc
    sourceRest 152962 = (sourceRest 152962).take 30 ++ (sourceRest 152962).drop 30 :=
      (List.take_append_drop 30 (sourceRest 152962)).symm
    _ = blockChars ++ (sourceRest 152962).drop 30 :=
      congrArg (fun part => part ++ (sourceRest 152962).drop 30) block_original_prefix
    _ = blockChars ++ sourceRest 152992 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 152962 30)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (sourceRest 152962)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 152992) :=
  (congrArg (fun chars => SourceJson.array (fuel + 20) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 152992) acc)

#print axioms array_chunk0048
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock006

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
