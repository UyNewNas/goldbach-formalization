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

namespace AllOriginalConstraintMinimaBlock004

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_before_reader"
  err.flush

noncomputable def chunk0032Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '/', '6', '4', '"', ',']
noncomputable def chunk0032Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['5', '/', '6', '4'])) :: ((.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (chunk0032Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_before_reader"
  err.flush

noncomputable def chunk0033Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '4', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '6', '1', '4', '0', '6', '6', '9', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0033Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['6', '1', '4', '0', '6', '6', '9', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '9', '4', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail) (chunk0033Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_before_reader"
  err.flush

noncomputable def chunk0034Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '6', '1', '/', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0034Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '2', '8', '1', '6', '1', '/', '7', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail) (chunk0034Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_before_reader"
  err.flush

noncomputable def chunk0035Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '3', '3', '/', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0035Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '7', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 44) (SourceJson.white tail) (chunk0035Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_before_reader"
  err.flush

noncomputable def chunk0036Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '5', '1', '5', '9', '0', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0036Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['9', '5', '1', '5', '9', '0', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail) (chunk0036Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_before_reader"
  err.flush

noncomputable def chunk0037Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '5', '2', '7', '5', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0037Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['2', '5', '4', '5', '2', '7', '5', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail) (chunk0037Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_before_reader"
  err.flush

noncomputable def chunk0038Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '3', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0038Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '9', '0', '3', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail) (chunk0038Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_before_reader"
  err.flush

noncomputable def chunk0039Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '1', '7', '1', '8', '6', '3', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '5', '9', '6', '9', '9', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0039Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '1', '8', '5', '9', '6', '9', '9', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['4', '1', '7', '1', '8', '6', '3', '/', '2', '5', '6', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail) (chunk0039Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0032Chars00 ++ chunk0033Chars00 ++ chunk0034Chars00 ++ chunk0035Chars00 ++ chunk0036Chars00 ++ chunk0037Chars00 ++ chunk0038Chars00 ++ chunk0039Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0039Push00 (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 52) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 52) (SourceJson.white (chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 52) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 50) (SourceJson.white (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))))) (chunk0032Push00 (acc)) := array_chunk0032 fuel (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 48) (SourceJson.white (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) (chunk0033Push00 (chunk0032Push00 (acc))) := array_chunk0033 fuel (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))) (chunk0032Push00 (acc))
    _ = SourceJson.array (fuel + 46) (SourceJson.white (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))) := array_chunk0034 fuel (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))) (chunk0033Push00 (chunk0032Push00 (acc)))
    _ = SourceJson.array (fuel + 44) (SourceJson.white (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))) := array_chunk0035 fuel (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))
    _ = SourceJson.array (fuel + 42) (SourceJson.white (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))) := array_chunk0036 fuel (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))
    _ = SourceJson.array (fuel + 40) (SourceJson.white (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))) := array_chunk0037 fuel (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))
    _ = SourceJson.array (fuel + 38) (SourceJson.white (chunk0039Chars00 ++ (tail))) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))))) := array_chunk0038 fuel (chunk0039Chars00 ++ (tail)) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))))
    _ = SourceJson.array (fuel + 36) (SourceJson.white tail) (blockPush acc) := array_chunk0039 fuel (tail) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 62270).take 344 = blockChars := by rfl

theorem block_original_split : sourceRest 62270 = blockChars ++ sourceRest 62614 := by
  calc
    sourceRest 62270 = (sourceRest 62270).take 344 ++ (sourceRest 62270).drop 344 :=
      (List.take_append_drop 344 (sourceRest 62270)).symm
    _ = blockChars ++ (sourceRest 62270).drop 344 :=
      congrArg (fun part => part ++ (sourceRest 62270).drop 344) block_original_prefix
    _ = blockChars ++ sourceRest 62614 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 62270 344)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 62270)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white (sourceRest 62614)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 52) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 62614) acc)

#print axioms array_chunk0032
#print axioms array_chunk0033
#print axioms array_chunk0034
#print axioms array_chunk0035
#print axioms array_chunk0036
#print axioms array_chunk0037
#print axioms array_chunk0038
#print axioms array_chunk0039
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock004

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
