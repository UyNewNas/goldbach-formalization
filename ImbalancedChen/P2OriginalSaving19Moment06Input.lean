/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19ArchiveMomentData06
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-! Exact compact production-FQN input and list-span interfaces. The data owner
and loader source bytes are unchanged from v4. This local environment reads the
byte-identical private fixture copy; no P1 path or P1 acceptance is claimed. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Parsing

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19PackedChars

noncomputable def momentChars06 : List Char := momentPacked06.toList
noncomputable def momentRest06 (n : Nat) : List Char := (momentPacked06.drop n).toList

theorem momentRest06_eq_drop (n : Nat) :
    momentRest06 n = momentChars06.drop n :=
  Tree.toList_drop momentPacked06 n

theorem momentRest06_drop (start count : Nat) :
    (momentRest06 start).drop count = momentRest06 (start + count) := by
  simp only [momentRest06_eq_drop, List.drop_drop]

theorem momentRest06_zero : momentRest06 0 = momentChars06 := by
  simpa only [List.drop_zero] using momentRest06_eq_drop 0

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 count_before_guard"
  err.flush

theorem momentPacked06_count : momentPacked06.count = 58376 := by
  decide +kernel

theorem momentChars06_length : momentChars06.length = 58376 :=
  (Tree.length_toList momentPacked06).trans momentPacked06_count

theorem momentRest06_end : momentRest06 58376 = [] := by
  rw [momentRest06_eq_drop]
  exact List.drop_eq_nil_of_le (by rw [momentChars06_length]; exact Nat.le_refl _)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 count_and_list_interfaces_complete"
  err.flush

#print axioms momentRest06_eq_drop
#print axioms momentRest06_drop
#print axioms momentRest06_zero
#print axioms momentPacked06_count
#print axioms momentChars06_length
#print axioms momentRest06_end

end ImbalancedChen.P2OriginalSaving19Moment06Parsing
