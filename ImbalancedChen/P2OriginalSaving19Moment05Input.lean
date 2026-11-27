import ImbalancedChen.P2OriginalSaving19ArchiveMomentData05
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-! Exact compact production-FQN input and list-span interfaces. The data owner
and loader source bytes are unchanged from v4. This local environment reads the
byte-identical private fixture copy; no P1 path or P1 acceptance is claimed. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Parsing

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19PackedChars

noncomputable def momentChars05 : List Char := momentPacked05.toList
noncomputable def momentRest05 (n : Nat) : List Char := (momentPacked05.drop n).toList

theorem momentRest05_eq_drop (n : Nat) :
    momentRest05 n = momentChars05.drop n :=
  Tree.toList_drop momentPacked05 n

theorem momentRest05_drop (start count : Nat) :
    (momentRest05 start).drop count = momentRest05 (start + count) := by
  simp only [momentRest05_eq_drop, List.drop_drop]

theorem momentRest05_zero : momentRest05 0 = momentChars05 := by
  simpa only [List.drop_zero] using momentRest05_eq_drop 0

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 count_before_guard"
  err.flush

theorem momentPacked05_count : momentPacked05.count = 28973 := by
  decide +kernel

theorem momentChars05_length : momentChars05.length = 28973 :=
  (Tree.length_toList momentPacked05).trans momentPacked05_count

theorem momentRest05_end : momentRest05 28973 = [] := by
  rw [momentRest05_eq_drop]
  exact List.drop_eq_nil_of_le (by rw [momentChars05_length]; exact Nat.le_refl _)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 count_and_list_interfaces_complete"
  err.flush

#print axioms momentRest05_eq_drop
#print axioms momentRest05_drop
#print axioms momentRest05_zero
#print axioms momentPacked05_count
#print axioms momentChars05_length
#print axioms momentRest05_end

end ImbalancedChen.P2OriginalSaving19Moment05Parsing
