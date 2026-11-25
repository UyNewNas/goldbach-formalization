import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00

/-! Compact production input count, exact rest interfaces and finite list reassembly.
The original parser certificates remain frozen; this owner only relates input
representations through exact complete character spans. -/
namespace ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def compactChars00 : List Char := geometryPacked00.toList
noncomputable def compactRest00 (n : Nat) : List Char := (geometryPacked00.drop n).toList

theorem compactRest00_eq_drop (n : Nat) :
    compactRest00 n = compactChars00.drop n :=
  Tree.toList_drop geometryPacked00 n

theorem compactRest00_drop (start count : Nat) :
    (compactRest00 start).drop count = compactRest00 (start + count) := by
  simp only [compactRest00_eq_drop, List.drop_drop]

theorem compactRest00_zero : compactRest00 0 = compactChars00 := by
  simpa only [List.drop_zero] using compactRest00_eq_drop 0

theorem geometryPacked00_count : geometryPacked00.count = 195134 := by
  decide +kernel

theorem compactChars00_length : compactChars00.length = 195134 :=
  (Tree.length_toList geometryPacked00).trans geometryPacked00_count

theorem compactRest00_end : compactRest00 195134 = [] := by
  rw [compactRest00_eq_drop]
  exact List.drop_eq_nil_of_le (by rw [compactChars00_length]; exact Nat.le_refl _)

/-- A proved finite prefix and the original remaining list reconstruct the input. -/
theorem list_drop_split_of_prefix {A : Type} (xs : List A) (start count : Nat)
    (chunk : List A) (h : (xs.drop start).take count = chunk) :
    xs.drop start = chunk ++ xs.drop (start + count) := by
  calc
    xs.drop start = (xs.drop start).take count ++ (xs.drop start).drop count :=
      (List.take_append_drop count (xs.drop start)).symm
    _ = chunk ++ (xs.drop start).drop count :=
      congrArg (fun part => part ++ (xs.drop start).drop count) h
    _ = chunk ++ xs.drop (start + count) := by rw [List.drop_drop]

#print axioms compactRest00_eq_drop
#print axioms compactRest00_drop
#print axioms compactRest00_zero
#print axioms geometryPacked00_count
#print axioms compactChars00_length
#print axioms compactRest00_end
#print axioms list_drop_split_of_prefix

end ImbalancedChen.P2OriginalSaving19GeometryPackedTransport
