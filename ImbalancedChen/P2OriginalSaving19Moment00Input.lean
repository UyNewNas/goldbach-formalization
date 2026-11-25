import ImbalancedChen.P2OriginalSaving19ArchiveMomentData00
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-! Exact compact production-FQN input and list-span interfaces. The data owner
and loader source bytes are unchanged from v4. This local environment reads the
byte-identical private fixture copy; no P1 path or P1 acceptance is claimed. -/
namespace ImbalancedChen.P2OriginalSaving19Moment00Parsing

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19PackedChars

noncomputable def momentChars00 : List Char := momentPacked00.toList
noncomputable def momentRest00 (n : Nat) : List Char := (momentPacked00.drop n).toList

theorem momentRest00_eq_drop (n : Nat) :
    momentRest00 n = momentChars00.drop n :=
  Tree.toList_drop momentPacked00 n

theorem momentRest00_drop (start count : Nat) :
    (momentRest00 start).drop count = momentRest00 (start + count) := by
  simp only [momentRest00_eq_drop, List.drop_drop]

theorem momentRest00_zero : momentRest00 0 = momentChars00 := by
  simpa only [List.drop_zero] using momentRest00_eq_drop 0

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 count_before_guard"
  err.flush

theorem momentPacked00_count : momentPacked00.count = 28999 := by
  decide +kernel

theorem momentChars00_length : momentChars00.length = 28999 :=
  (Tree.length_toList momentPacked00).trans momentPacked00_count

theorem momentRest00_end : momentRest00 28999 = [] := by
  rw [momentRest00_eq_drop]
  exact List.drop_eq_nil_of_le (by rw [momentChars00_length]; exact Nat.le_refl _)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT00 count_and_list_interfaces_complete"
  err.flush

#print axioms momentRest00_eq_drop
#print axioms momentRest00_drop
#print axioms momentRest00_zero
#print axioms momentPacked00_count
#print axioms momentChars00_length
#print axioms momentRest00_end

end ImbalancedChen.P2OriginalSaving19Moment00Parsing
