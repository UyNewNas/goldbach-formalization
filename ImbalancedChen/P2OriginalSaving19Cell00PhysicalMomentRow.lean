import ImbalancedChen.P2OriginalSaving19RationalSimplexBridge
import ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic
import ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge

/-! Candidate physical attachment of all original Cell00 floor records.
The saved maximum of old and new Q96 is retained. No integral is a premise. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00PhysicalMomentRow
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19HigherMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19RationalSimplexBridge
open P2OriginalSaving19Geometry00BoundedAccess
open P2OriginalSaving19Moment00Decoding
open P2OriginalSaving19Cell00AllOriginalFloorBridge

def originalMomentRow (r : Fin 56) : P2OriginalSaving19Archive.MomentRecord :=
  momentConcrete00.rows[r.val]!

def row (r : Fin 56) : AlgebraicMomentRow :=
  algebraicRow (boundedRowVertex r) (boundedRow r) (originalMoments r)
    (P2OriginalSaving19Cell00AllRowArithmetic.all_bounded_row_data_checks r)
    (original_first_moment r) (fun _ _ _ _ => rfl)

def physicalSimplex (r : Fin 56) : Set Point := support (row r).linear (row r).base

theorem simplex_vertices (r : Fin 56) :
    vertices (row r).linear (row r).base = fun i => realPoint (boundedRowVertex r i) :=
  original_vertices (boundedRowVertex r)
    (P2OriginalSaving19Cell00AllRowArithmetic.all_bounded_row_data_checks r).1

theorem stored_floor_bound (r : Fin 56) :
    ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ) ≤
      ∫ t in physicalSimplex r, conservativeDensity t := by
  have h := algebraicRowFloor_sound (row r)
  change ((((max
    (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96
      (P2OriginalSaving19RowNumericsPure.massOf (boundedRow r))
      (P2OriginalSaving19RowNumericsPure.meansOf (boundedRow r)))
    (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
      (P2OriginalSaving19RowNumericsPure.massOf (boundedRow r))
      (P2OriginalSaving19RowNumericsPure.meansOf (boundedRow r))
      (originalMoments r)) : ℤ) : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ) ≤ _ at h
  rw [← original_saved_new_Q96 r] at h
  exact h

theorem sum_stored_floor_bound :
    (∑ r : Fin 56,
      ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ)) ≤
      ∑ r : Fin 56, ∫ t in physicalSimplex r, conservativeDensity t :=
  Finset.sum_le_sum (fun r _ => stored_floor_bound r)

#print axioms simplex_vertices
#print axioms stored_floor_bound
#print axioms sum_stored_floor_bound
end
end ImbalancedChen.P2OriginalSaving19Cell00PhysicalMomentRow
