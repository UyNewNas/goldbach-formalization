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

namespace AllOriginalConstraintMinimaBlock000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '3', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '4', '3', '3', '2', '3', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '4', '3', '3', '2', '3', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '9', '3', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 116) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 114) (SourceJson.white tail) (chunk0000Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '8', '2', '9', '5', '6', '9', '4', '1', '/', '3', '6', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '8', '4', '8', '4', '2', '5', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['8', '4', '8', '4', '2', '5', '1', '/', '3', '4', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['8', '2', '9', '5', '6', '9', '4', '1', '/', '3', '6', '7', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 114) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 112) (SourceJson.white tail) (chunk0001Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '3', '7', '5', '0', '0', '0', '"', ',']
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '3', '7', '5', '0', '0', '0'])) :: ((.str (String.ofList ['1', '/', '3', '7', '5', '0', '0', '0'])) :: (acc))

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 112) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 110) (SourceJson.white tail) (chunk0002Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '4', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '3', '7', '5', '0', '0', '0', '"', ',']
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '3', '7', '5', '0', '0', '0'])) :: ((.str (String.ofList ['3', '2', '8', '1', '4', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 110) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 108) (SourceJson.white tail) (chunk0003Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_before_reader"
  err.flush

noncomputable def chunk0004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0004Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['0'])) :: (acc))

theorem array_chunk0004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 108) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 106) (SourceJson.white tail) (chunk0004Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_before_reader"
  err.flush

noncomputable def chunk0005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '9', '3', '7', '9', '/', '4', '8', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '9', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0005Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '7', '6', '5', '9', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['9', '9', '3', '7', '9', '/', '4', '8', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 106) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 104) (SourceJson.white tail) (chunk0005Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_before_reader"
  err.flush

noncomputable def chunk0006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '8', '4', '5', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '2', '4', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0006Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '9', '2', '2', '4', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['9', '8', '4', '5', '3', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 104) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 102) (SourceJson.white tail) (chunk0006Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_before_reader"
  err.flush

noncomputable def chunk0007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0007Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: (acc))

theorem array_chunk0007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 102) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 100) (SourceJson.white tail) (chunk0007Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00 ++ chunk0002Chars00 ++ chunk0003Chars00 ++ chunk0004Chars00 ++ chunk0005Chars00 ++ chunk0006Chars00 ++ chunk0007Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0007Push00 (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 116) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 100) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 116) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 116) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 116) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 114) (SourceJson.white (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 112) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (chunk0001Push00 (chunk0000Push00 (acc))) := array_chunk0001 fuel (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0000Push00 (acc))
    _ = SourceJson.array (fuel + 110) (SourceJson.white (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))) := array_chunk0002 fuel (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0001Push00 (chunk0000Push00 (acc)))
    _ = SourceJson.array (fuel + 108) (SourceJson.white (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))) := array_chunk0003 fuel (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))
    _ = SourceJson.array (fuel + 106) (SourceJson.white (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))) := array_chunk0004 fuel (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))
    _ = SourceJson.array (fuel + 104) (SourceJson.white (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))) := array_chunk0005 fuel (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))
    _ = SourceJson.array (fuel + 102) (SourceJson.white (chunk0007Chars00 ++ (tail))) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))) := array_chunk0006 fuel (chunk0007Chars00 ++ (tail)) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))
    _ = SourceJson.array (fuel + 100) (SourceJson.white tail) (blockPush acc) := array_chunk0007 fuel (tail) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 60902).take 321 = blockChars := by rfl

theorem block_original_split : sourceRest 60902 = blockChars ++ sourceRest 61223 := by
  calc
    sourceRest 60902 = (sourceRest 60902).take 321 ++ (sourceRest 60902).drop 321 :=
      (List.take_append_drop 321 (sourceRest 60902)).symm
    _ = blockChars ++ (sourceRest 60902).drop 321 :=
      congrArg (fun part => part ++ (sourceRest 60902).drop 321) block_original_prefix
    _ = blockChars ++ sourceRest 61223 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 60902 321)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 60902)) acc =
      SourceJson.array (fuel + 100) (SourceJson.white (sourceRest 61223)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 116) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 61223) acc)

#print axioms array_chunk0000
#print axioms array_chunk0001
#print axioms array_chunk0002
#print axioms array_chunk0003
#print axioms array_chunk0004
#print axioms array_chunk0005
#print axioms array_chunk0006
#print axioms array_chunk0007
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock000

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
