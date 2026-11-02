import ImbalancedChen.P2OriginalFourteenCausalHistoryMesh
import ImbalancedChen.P2OriginalSaving16FourteenPhysicalAtlas

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal fourteen-cell specialization, consuming the geometry owner's
original rational 96-row atlas. Every positive trim is compact and lies
in the real source; every source point survives some positive trim.
Thus the common history precision is constructed on actual whole-source
inner trims, not on an unspecified or potentially unrelated compact set.
The integral loss as the trim tends to zero remains a separate estimate.
-/
namespace ImbalancedChen.P2OriginalSaving16TrimmedHistory
noncomputable section
open scoped Classical BigOperators
open Set
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalFourteenCausalHistoryMesh

/-- Only the original nonconstant rows are trimmed. The two constant
identities are absent from the 96-row source and are never made strict. -/
def trimmedCell (delta : ℝ) (c : Cell) : Set Point :=
  coordinateBox ∩ ⋂ k : Fin 96, {t | delta ≤ evalRow (rows c k).2 t}

def trimmedRegion (delta : ℝ) : Set Point := ⋃ c : Cell, trimmedCell delta c

theorem isCompact_trimmedCell (delta : ℝ) (c : Cell) : IsCompact (trimmedCell delta c) := by
  apply isCompact_coordinateBox.of_isClosed_subset
  · exact isCompact_coordinateBox.isClosed.inter
      (isClosed_iInter (fun k => isClosed_le continuous_const (continuous_evalRow (rows c k).2)))
  · exact inter_subset_left

theorem isCompact_trimmedRegion (delta : ℝ) : IsCompact (trimmedRegion delta) :=
  isCompact_iUnion (fun c => isCompact_trimmedCell delta c)

theorem trimmedCell_subset_cell (delta : ℝ) (hdelta : 0 < delta) (c : Cell) :
    trimmedCell delta c ⊆ cell c := by
  intro t ht k
  exact hdelta.trans_le (mem_iInter.mp ht.2 k)

theorem trimmedRegion_subset_region (delta : ℝ) (hdelta : 0 < delta) :
    trimmedRegion delta ⊆ region := by
  intro t ht
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨c, trimmedCell_subset_cell delta hdelta c hc⟩

/-- Every original physical point survives one fixed positive trim.
This proof minimizes finitely many actual source slacks symbolically;
it does not run the producer or evaluate a numerical certificate. -/
theorem region_point_survives_trim {t : Point} (ht : t ∈ region) :
    ∃ delta : ℝ, 0 < delta ∧ t ∈ trimmedRegion delta := by
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  have hpos : ∀ k ∈ (Set.univ : Set (Fin 96)), 0 < evalRow (rows c k).2 t :=
    fun k _ => hc k
  obtain ⟨delta, hdelta, hfloor⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Fin 96))).exists_forall_le'
      (show ContinuousOn (fun k : Fin 96 => evalRow (rows c k).2 t) Set.univ from
        continuous_of_discreteTopology.continuousOn) hpos
  refine ⟨delta, hdelta, mem_iUnion.mpr ⟨c, ?_⟩⟩
  exact ⟨(cell_subset_safeCarrier c hc).1,
    mem_iInter.mpr (fun k => hfloor k (mem_univ k))⟩

theorem region_eq_positive_trims :
    region = {t | ∃ delta : ℝ, 0 < delta ∧ t ∈ trimmedRegion delta} := by
  ext t
  constructor
  · exact region_point_survives_trim
  · rintro ⟨delta, hdelta, ht⟩
    exact trimmedRegion_subset_region delta hdelta ht

/-- One finite first-three mesh for ALL actual fourteen trimmed cells,
with arbitrarily requested cap accuracy and no history-gap premise. -/
theorem actual_fourteen_trim_common_history_precision
    (delta : ℝ) (hdelta : 0 < delta) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ 3 * tau < epsilon ∧ ∀ t ∈ trimmedRegion delta,
      pointLabel tau t ∈ labels tau ∧
      3 * t 0 < finiteThirdCap tau t ∧
      oddCube t 2 < finiteThirdCap tau t ∧
      oddCube t 4 < finiteThirdCap tau t ∧
      oddCube t 6 < finiteThirdCap tau t ∧
      0 < R t - finiteThirdCap tau t ∧ R t - finiteThirdCap tau t < epsilon := by
  apply exists_common_history_precision_with_error
    P4AOriginalAscending14Literal42.literalPattern (trimmedRegion delta)
    (isCompact_trimmedRegion delta) _ epsilon hepsilon
  intro t ht
  exact region_selectedFamilyGuard (trimmedRegion_subset_region delta hdelta ht)

/-- Actual source specialization with the correct quantifier order:
precision is fixed before N, its prime history, and its sixth exponent. -/
theorem actual_fourteen_trim_causal_parent_history (delta : ℝ) (hdelta : 0 < delta) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ N : ℝ, ∀ pre : List ℕ, pre.length = 8 →
      primeHistoryLogCoordinates N 8 pre ∈ trimmedRegion delta → ∀ current : ℝ,
      causalThirdExponent tau N pre ≤ current →
      current ≤ R (primeHistoryLogCoordinates N 8 pre) →
      CurrentParentGuard (primeHistoryLogCoordinates N 8 pre) current := by
  apply common_precision_supplies_parent_history
    P4AOriginalAscending14Literal42.literalPattern (trimmedRegion delta)
    (isCompact_trimmedRegion delta)
  intro t ht
  exact region_selectedFamilyGuard (trimmedRegion_subset_region delta hdelta ht)

end
end ImbalancedChen.P2OriginalSaving16TrimmedHistory
