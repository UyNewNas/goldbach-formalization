import ImbalancedChen.P2OriginalSaving16FourteenPhysicalAtlas
import ImbalancedChen.P4AOriginalFull87PrefixBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Bind the ORIGINAL saving16 source, not just its fourteen labels, to the
ascending fourteen members of the original87 source dictionary. The 96
rows retain their original order in every cell. The closed rational-row
identity below is UNEVALUATED; no centre, facet, moment or numerical
saving is checked here. This is source membership, not a construction of
the full actual sixth parent or of the compiled final policy.
-/

namespace ImbalancedChen.P2OriginalSaving16Full87SourceBinding

noncomputable section
open scoped Classical BigOperators
open Set

abbrev Point := Fin 8 → ℝ
abbrev AtlasCell := P2OriginalSaving16FourteenPhysicalAtlas.Cell
abbrev FullCell := P4AOriginalFull87SourceDictionary.Cell

/-- Original IDs 0,1,2 followed by 3,4,5,6,8,...,14. No seed7. -/
def atlasCell : Fin 14 → AtlasCell :=
  ![.inl 0, .inl 1, .inl 2, .inr 0, .inr 1, .inr 2, .inr 3,
    .inr 4, .inr 5, .inr 6, .inr 7, .inr 8, .inr 9, .inr 10]

def sourceCell (i : Fin 14) : FullCell := .remaining (.ascending i)

theorem atlasCell_bijective : Function.Bijective atlasCell := by decide

/-- The published slot is the same original navigation ID. This small
index identity alone is not used as a source-membership proof. -/
theorem original_id_eq (i : Fin 14) :
    (P2OriginalSaving16FourteenPhysicalAtlas.sourceId (atlasCell i)).val =
      (P4AOriginalFull87SourceDictionary.globalIndex (sourceCell i)).val := by
  fin_cases i <;> decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- All 1344 ordered original rational rows, coordinate by coordinate.
UNEVALUATED structural identity; it contains no real-geometry test. -/
theorem original_rows_exact : ∀ (i : Fin 14) (k : Fin 96) (j : Fin 9),
    (P2OriginalSaving16FourteenPhysicalAtlas.rows (atlasCell i) k).2 j =
      P4AOriginalAscendingFourteenAffineSource.rows i k j := by decide

theorem original_row_eq (i : Fin 14) (k : Fin 96) :
    (P2OriginalSaving16FourteenPhysicalAtlas.rows (atlasCell i) k).2 =
      P4AOriginalAscendingFourteenAffineSource.rows i k :=
  funext (original_rows_exact i k)

/-- Full source equivalence uses every original affine row, rather than
the weaker physical guard or a chosen tuple of sufficient inequalities. -/
theorem sourceRows_iff_full87_source (i : Fin 14) (t : Point) :
    P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) t ↔
      P4AOriginalFull87SourceDictionary.Source (sourceCell i) t := by
  change (∀ k : Fin 96, 0 < P4AOriginalSeed7Unequal15Literal.evalAffine
      (P2OriginalSaving16FourteenPhysicalAtlas.rows (atlasCell i) k).2 t) ↔
    (∀ k : Fin 96, 0 < P4AOriginalRemainingEighthSources.evalRow
      (P4AOriginalAscendingFourteenAffineSource.rows i k) t)
  simp only [original_row_eq]
  rfl

/-- The actual whole saving16 source is precisely the union of these
fourteen original87 members. This makes no claim about later dispatch. -/
theorem mem_region_iff_full87_source (t : Point) :
    t ∈ P2OriginalSaving16FourteenPhysicalAtlas.region ↔
      ∃ i : Fin 14, P4AOriginalFull87SourceDictionary.Source (sourceCell i) t := by
  constructor
  · intro ht
    obtain ⟨c, hc⟩ := mem_iUnion.mp ht
    obtain ⟨i, rfl⟩ := atlasCell_bijective.2 c
    exact ⟨i, (sourceRows_iff_full87_source i t).mp hc⟩
  · rintro ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨atlasCell i, (sourceRows_iff_full87_source i t).mpr hi⟩

theorem region_eq_full87_sourceUnion :
    P2OriginalSaving16FourteenPhysicalAtlas.region =
      {t : Point | ∃ i : Fin 14,
        P4AOriginalFull87SourceDictionary.Source (sourceCell i) t} := by
  ext t
  exact mem_region_iff_full87_source t

/-- The same actual source has mask129 and the original unaltered cap. -/
theorem source_selected_and_cap (i : Fin 14) (t : Point)
    (hs : P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) t) :
    P4AOriginalFull87SourceDictionary.selected (sourceCell i) = {0, 7} ∧
      P4AOriginalFull87SourceDictionary.newCap (sourceCell i) t =
        P2OriginalAscendingEighthCapDictionary.M t ∧
      P4AOriginalFull87SourceDictionary.comparison (sourceCell i) t =
        P2OriginalAscendingEighthCapDictionary.R t := by
  constructor
  · rfl
  constructor
  · have ha := (P2OriginalSaving16FourteenPhysicalAtlas.sourceRows_cellGuard
      (atlasCell i) t hs).new_ascending
    rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
    norm_num [sourceCell, P4AOriginalFull87SourceDictionary.newCap,
      P4AOriginalRemainingEighthSources.newCap,
      P4AOriginalRemainingEighthSources.descendingNew,
      P4AOriginalRemainingEighthSources.selectedSum,
      P4AOriginalRemainingEighthSources.selected,
      P4AOriginalRemainingEighthSources.eta,
      P2OriginalAscendingEighthCapDictionary.selectedSum,
      P2OriginalAscendingEighthCapDictionary.eta]
  · rfl

/-- Own-prefix ideal-third histories follow from actual atlas membership.
The conclusion deliberately names the ideal third, not actual lambda6. -/
theorem source_histories_at_own_third_prefix
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8) (i : Fin 14)
    (hs : P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i)
      (primeHistoryLogCoordinates N 8 pre)) :
    ∀ j : Fin 4, P4AOriginalRemainingEighthSources.history
      (primeHistoryLogCoordinates N 8 pre) j <
        P4AOriginalFull87PrefixBinding.idealThirdPrefix N (rosserAncestor 3 pre) :=
  P4AOriginalFull87PrefixBinding.source_histories_at_own_third_prefix
    N pre hlen (sourceCell i) ((sourceRows_iff_full87_source i _).mp hs)

end
end ImbalancedChen.P2OriginalSaving16Full87SourceBinding
