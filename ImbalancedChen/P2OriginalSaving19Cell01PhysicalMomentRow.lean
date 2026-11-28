import ImbalancedChen.P2OriginalSaving19RationalSimplexBridge
import ImbalancedChen.P2OriginalSaving19Cell01AllRowArithmetic

/-! Candidate physical attachment of every original Cell01 floor record.
The saved max(old,new) Q96 is retained and no integral is a premise.
This owner awaits the 144-row floor bridge and its own compilation checks. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01PhysicalMomentRow
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19HigherMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19RationalSimplexBridge
open P2OriginalSaving19Geometry01BoundedAccess
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Cell01OriginalFloorInterface
open P2OriginalSaving19Cell01AllOriginalFloorBridge

def originalMomentRow (r : Fin 144) : P2OriginalSaving19Archive.MomentRecord :=
  rawMomentRow r

def originalMoments (r : Fin 144) (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19HigherMoments.rationalMoment
    (fun i => gapQ (boundedRowVertex r i))
    (fun i => 1 - factorsQ (boundedRowVertex r i) j / topsOf (boundedRow r) j) k

theorem raw_moments_eq (r : Fin 144) : rawOriginalMoments r = originalMoments r := by
  have hv : rawVertices r = boundedRowVertex r := by
    funext i j
    exact P2OriginalSaving19Cell01OriginalFloorInterface.raw_vertex_no_fallback r i j
  funext j k
  unfold rawOriginalMoments originalMoments
  simp only [hv, raw_geometry_row_no_fallback, topsOf]

theorem original_first_moment (r : Fin 144) (j : Fin 10) :
    originalMoments r j 1 = 1 - meansOf (boundedRow r) j / topsOf (boundedRow r) j := by
  have h := (all_original_floor_formula r).1 j
  simp only [raw_geometry_row_no_fallback, raw_moments_eq] at h
  exact h

theorem original_saved_new_Q96 (r : Fin 144) :
    (originalMomentRow r).newFloorQ96 = max
      (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96
        (massOf (boundedRow r)) (meansOf (boundedRow r)))
      (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
        (massOf (boundedRow r)) (meansOf (boundedRow r)) (originalMoments r)) := by
  have h := (all_original_floor_formula r).2.2.2.2
  simp only [raw_geometry_row_no_fallback, raw_moments_eq] at h
  exact h

def row (r : Fin 144) : AlgebraicMomentRow :=
  algebraicRow (boundedRowVertex r) (boundedRow r) (originalMoments r)
    (P2OriginalSaving19Cell01AllRowArithmetic.all_bounded_row_data_checks r)
    (original_first_moment r) (fun _ _ _ _ => rfl)

def physicalSimplex (r : Fin 144) : Set Point := support (row r).linear (row r).base

theorem simplex_vertices (r : Fin 144) :
    vertices (row r).linear (row r).base = fun i => realPoint (boundedRowVertex r i) :=
  original_vertices (boundedRowVertex r)
    (P2OriginalSaving19Cell01AllRowArithmetic.all_bounded_row_data_checks r).1

theorem stored_floor_bound (r : Fin 144) :
    ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ) ≤
      ∫ t in physicalSimplex r, conservativeDensity t := by
  have h := algebraicRowFloor_sound (row r)
  change ((((max
    (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96
      (massOf (boundedRow r)) (meansOf (boundedRow r)))
    (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
      (massOf (boundedRow r)) (meansOf (boundedRow r))
      (originalMoments r)) : ℤ) : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ) ≤ _ at h
  rw [← original_saved_new_Q96 r] at h
  exact h

theorem sum_stored_floor_bound :
    (∑ r : Fin 144,
      ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ)) ≤
      ∑ r : Fin 144, ∫ t in physicalSimplex r, conservativeDensity t :=
  Finset.sum_le_sum (fun r _ => stored_floor_bound r)

#print axioms raw_moments_eq
#print axioms original_first_moment
#print axioms original_saved_new_Q96
#print axioms simplex_vertices
#print axioms stored_floor_bound
#print axioms sum_stored_floor_bound
end
end ImbalancedChen.P2OriginalSaving19Cell01PhysicalMomentRow
