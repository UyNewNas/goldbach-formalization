import ImbalancedChen.P2OriginalSaving19ArchiveMomentData01
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-! Exact compact production-FQN input and list-span interfaces. The data owner
and loader source bytes are unchanged from v4. This local environment reads the
byte-identical private fixture copy; no P1 path or P1 acceptance is claimed. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Parsing

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19PackedChars

noncomputable def momentChars01 : List Char := momentPacked01.toList
noncomputable def momentRest01 (n : Nat) : List Char := (momentPacked01.drop n).toList

theorem momentRest01_eq_drop (n : Nat) :
    momentRest01 n = momentChars01.drop n :=
  Tree.toList_drop momentPacked01 n

theorem momentRest01_drop (start count : Nat) :
    (momentRest01 start).drop count = momentRest01 (start + count) := by
  simp only [momentRest01_eq_drop, List.drop_drop]

theorem momentRest01_zero : momentRest01 0 = momentChars01 := by
  simpa only [List.drop_zero] using momentRest01_eq_drop 0

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 count_before_guard"
  err.flush

theorem momentPacked01_count : momentPacked01.count = 75094 := by
  decide +kernel

theorem momentChars01_length : momentChars01.length = 75094 :=
  (Tree.length_toList momentPacked01).trans momentPacked01_count

theorem momentRest01_end : momentRest01 75094 = [] := by
  rw [momentRest01_eq_drop]
  exact List.drop_eq_nil_of_le (by rw [momentChars01_length]; exact Nat.le_refl _)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 count_and_list_interfaces_complete"
  err.flush

#print axioms momentRest01_eq_drop
#print axioms momentRest01_drop
#print axioms momentRest01_zero
#print axioms momentPacked01_count
#print axioms momentChars01_length
#print axioms momentRest01_end

end ImbalancedChen.P2OriginalSaving19Moment01Parsing
