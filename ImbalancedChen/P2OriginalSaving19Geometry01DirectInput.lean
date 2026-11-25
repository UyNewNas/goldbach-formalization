import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData01
import ImbalancedChen.P2OriginalSaving19ParseFromValue00

/-! Cell 01: direct packed input and exact remaining-list interfaces.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def sourceChars : List Char := geometryPacked01.toList
noncomputable def sourceRest (n : Nat) : List Char := (geometryPacked01.drop n).toList

theorem sourceRest_eq_drop (n : Nat) : sourceRest n = sourceChars.drop n :=
  Tree.toList_drop geometryPacked01 n

theorem sourceRest_drop (start count : Nat) :
    (sourceRest start).drop count = sourceRest (start + count) := by
  simp only [sourceRest_eq_drop, List.drop_drop]

theorem sourceRest_zero : sourceRest 0 = sourceChars := by
  simpa only [List.drop_zero] using sourceRest_eq_drop 0

theorem sourcePacked_count : geometryPacked01.count = 470901 := by decide +kernel

theorem sourceChars_length : sourceChars.length = 470901 :=
  (Tree.length_toList geometryPacked01).trans sourcePacked_count

theorem sourceRest_end : sourceRest 470901 = [] := by
  rw [sourceRest_eq_drop]
  exact List.drop_eq_nil_of_le (by rw [sourceChars_length]; exact Nat.le_refl _)

#print axioms sourceRest_eq_drop
#print axioms sourceRest_drop
#print axioms sourceRest_zero
#print axioms sourcePacked_count
#print axioms sourceChars_length
#print axioms sourceRest_end

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
