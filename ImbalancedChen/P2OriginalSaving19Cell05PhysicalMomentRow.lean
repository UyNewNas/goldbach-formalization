import ImbalancedChen.P2OriginalSaving19RationalSimplexBridge
import ImbalancedChen.P2OriginalSaving19Cell05HigherMomentEncoding

/-! Candidate attachment of original Cell05 numerical records to their
actual physical simplex integrals. Coverage and disjointness stay separate. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05PhysicalMomentRow
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19HigherMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19RationalSimplexBridge
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19Cell05AllRowArithmetic
open P2OriginalSaving19Cell05MomentBounds
open P2OriginalSaving19Cell05HigherMomentEncoding
open P2OriginalSaving19Cell05MomentQ80Pilot
open P2OriginalSaving19Cell05MomentQ96RecordChecks

def row (r : Fin 56) : AlgebraicMomentRow :=
  algebraicRow (boundedRowVertex05 r) (boundedRow05 r) (prefixMoment r)
    (all_bounded_row_data_checks r) (prefixMoment_one r)
    (fun j k _ hk => all_prefix_moments r j k hk)

def physicalSimplex (r : Fin 56) : Set Point := support (row r).linear (row r).base

theorem simplex_vertices (r : Fin 56) :
    vertices (row r).linear (row r).base = fun i => realPoint (boundedRowVertex05 r i) :=
  original_vertices (boundedRowVertex05 r) (all_bounded_row_data_checks r).1

theorem actual_higher_moments (r : Fin 56) (j : Fin 10) (k : ℕ)
    (hk : 2 ≤ k) (hk6 : k ≤ 6) :
    (prefixMoment r j k : ℝ) = ∫ t,
      P2DegreeSixLogGapSoundnessSourceOnly.scaledDeviation
        ((row r).topsQ j : ℝ) (fun t => factors t j) t ^ k
        ∂simplexProbability (row r).linear (row r).base :=
  higherPowerMoments_of_encoding (row r) j k hk hk6

theorem stored_floor_bound (r : Fin 56) :
    ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ) ≤
      ∫ t in physicalSimplex r, conservativeDensity t := by
  have h := row_computed_Q96_sound (row r).toMomentRow
  change (P2OriginalLogMomentQ96ArithmeticPure.simplexLowerQ96
    (P2OriginalSaving19RowNumericsPure.massOf (boundedRow05 r))
    (P2OriginalSaving19RowNumericsPure.meansOf (boundedRow05 r))
    (prefixMoment r) : ℝ) ≤ ∫ t in physicalSimplex r, conservativeDensity t at h
  rw [← stored_lower_eq_computed r] at h
  exact h

/-- A sum of actual simplex integrals. No assertion identifies this sum
with an integral over a union or over the original selected source cell. -/
theorem sum_stored_floor_bound :
    (∑ r : Fin 56,
      ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ)) ≤
      ∑ r : Fin 56, ∫ t in physicalSimplex r, conservativeDensity t :=
  Finset.sum_le_sum (fun r _ => stored_floor_bound r)

#print axioms simplex_vertices
#print axioms actual_higher_moments
#print axioms stored_floor_bound
#print axioms sum_stored_floor_bound
end
end ImbalancedChen.P2OriginalSaving19Cell05PhysicalMomentRow
