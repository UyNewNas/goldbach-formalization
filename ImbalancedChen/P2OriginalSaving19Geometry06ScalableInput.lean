import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData06
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Cell 06: direct packed input and exact remaining-list interfaces.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def sourceChars : List Char := geometryPacked06.toList
noncomputable def sourceRest (n : Nat) : List Char := (geometryPacked06.drop n).toList

theorem sourceRest_eq_drop (n : Nat) : sourceRest n = sourceChars.drop n :=
  Tree.toList_drop geometryPacked06 n

theorem sourceRest_drop (start count : Nat) :
    (sourceRest start).drop count = sourceRest (start + count) := by
  simp only [sourceRest_eq_drop, List.drop_drop]

theorem sourceRest_zero : sourceRest 0 = sourceChars := by
  simpa only [List.drop_zero] using sourceRest_eq_drop 0

theorem sourcePacked_count : geometryPacked06.count = 335849 := by decide +kernel

theorem sourceChars_length : sourceChars.length = 335849 :=
  (Tree.length_toList geometryPacked06).trans sourcePacked_count

theorem sourceRest_end : sourceRest 335849 = [] := by
  rw [sourceRest_eq_drop]
  exact List.drop_eq_nil_of_le (by rw [sourceChars_length]; exact Nat.le_refl _)

#print axioms sourceRest_eq_drop
#print axioms sourceRest_drop
#print axioms sourceRest_zero
#print axioms sourcePacked_count
#print axioms sourceChars_length
#print axioms sourceRest_end

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
