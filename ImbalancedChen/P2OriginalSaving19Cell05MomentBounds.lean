import ImbalancedChen.P2OriginalSaving19Cell05GeometryCertificate
import ImbalancedChen.P2OriginalSaving19FiniteWeightedMean
import ImbalancedChen.P2OriginalSaving19PrefixFirstMoment

/-! Quantitative bounds for the original Cell05 moment normalizations.
All coordinates and tops are the original parser-bound geometry data.
No stored moment-refinement field or integral estimate is a premise. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05MomentBounds
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19Cell05AllRowArithmetic
open P2OriginalSaving19Cell05GeometryCertificate

noncomputable section

theorem row_mean_bounds (r : Fin 56) (j : Fin 10) :
    (53 : ℚ) / 13824 ≤ meansOf (boundedRow05 r) j ∧
      meansOf (boundedRow05 r) j ≤ topsOf (boundedRow05 r) j := by
  rw [(all_bounded_row_data_checks r).2.2.2.2.2.1 j]
  apply P2OriginalSaving19FiniteWeightedMean.bounds
    (fun i => gapQ (boundedRowVertex05 r i))
    (fun i => factorsQ (boundedRowVertex05 r i) j)
    (row_gap_nonneg r) (all_row_gaps r).1
  intro i
  exact ⟨row_factor_lower r i j,
    (all_bounded_row_data_checks r).2.2.2.2.2.2.1 i j⟩

def deviation (r : Fin 56) (j : Fin 10) (i : Fin 9) : ℚ :=
  1 - factorsQ (boundedRowVertex05 r i) j / topsOf (boundedRow05 r) j

def rangeTop (r : Fin 56) (j : Fin 10) : ℚ :=
  1 - ((53 : ℚ) / 13824) / topsOf (boundedRow05 r) j

theorem deviation_nonneg (r : Fin 56) (j : Fin 10) (i : Fin 9) :
    0 ≤ deviation r j i := by
  apply sub_nonneg.mpr
  exact (div_le_one (row_top_pos r j)).2
    ((all_bounded_row_data_checks r).2.2.2.2.2.2.1 i j)

theorem deviation_le_rangeTop (r : Fin 56) (j : Fin 10) (i : Fin 9) :
    deviation r j i ≤ rangeTop r j := by
  exact sub_le_sub_left
    (div_le_div_of_nonneg_right (row_factor_lower r i j) (le_of_lt (row_top_pos r j))) 1

theorem rangeTop_lt_one (r : Fin 56) (j : Fin 10) : rangeTop r j < 1 := by
  have h : 0 < ((53 : ℚ) / 13824) / topsOf (boundedRow05 r) j :=
    div_pos (by norm_num) (row_top_pos r j)
  exact sub_lt_self _ h

theorem mean_deviation_bounds (r : Fin 56) (j : Fin 10) :
    0 ≤ 1 - meansOf (boundedRow05 r) j / topsOf (boundedRow05 r) j ∧
    1 - meansOf (boundedRow05 r) j / topsOf (boundedRow05 r) j ≤ rangeTop r j := by
  constructor
  · exact sub_nonneg.mpr ((div_le_one (row_top_pos r j)).2 (row_mean_bounds r j).2)
  · exact sub_le_sub_left
      (div_le_div_of_nonneg_right (row_mean_bounds r j).1 (le_of_lt (row_top_pos r j))) 1

theorem all_deviation_ranges (r : Fin 56) (j : Fin 10) :
    (∀ i : Fin 9, deviation r j i ∈ Set.Icc 0 (rangeTop r j)) ∧ rangeTop r j < 1 :=
  ⟨fun i => ⟨deviation_nonneg r j i, deviation_le_rangeTop r j i⟩, rangeTop_lt_one r j⟩

/-- Exact first-order weighted expression on the original nine vertices.
An integral interpretation still belongs to the higher-moment semantic owner. -/
def firstMomentExpression (r : Fin 56) (j : Fin 10) : ℚ :=
  ((∑ i, deviation r j i) +
    (∑ i, gapQ (boundedRowVertex05 r i) * deviation r j i) /
      gapSumOf (boundedRowVertex05 r)) / 10

theorem firstMomentExpression_eq (r : Fin 56) (j : Fin 10) :
    firstMomentExpression r j = 1 - meansOf (boundedRow05 r) j / topsOf (boundedRow05 r) j := by
  rw [(all_bounded_row_data_checks r).2.2.2.2.2.1 j]
  exact P2OriginalSaving19FiniteWeightedMean.deviation_first
    (fun i => gapQ (boundedRowVertex05 r i))
    (fun i => factorsQ (boundedRowVertex05 r i) j) (topsOf (boundedRow05 r) j)
    (ne_of_gt (all_row_gaps r).1) (ne_of_gt (row_top_pos r j))

theorem firstMomentExpression_range (r : Fin 56) (j : Fin 10) :
    firstMomentExpression r j ∈ Set.Icc 0 (rangeTop r j) := by
  rw [firstMomentExpression_eq]
  exact mean_deviation_bounds r j

def prefixMoment (r : Fin 56) (j : Fin 10) (k : ℕ) : ℚ :=
  P2OriginalSaving19PrefixFirstMoment.encodedMoment
    (fun i => gapQ (boundedRowVertex05 r i)) (deviation r j) k

theorem prefixMoment_zero (r : Fin 56) (j : Fin 10) : prefixMoment r j 0 = 1 :=
  P2OriginalSaving19PrefixFirstMoment.encoded_zero _ _ (row_gap_nonneg r) (all_row_gaps r).1

theorem prefixMoment_one (r : Fin 56) (j : Fin 10) :
    prefixMoment r j 1 = 1 - meansOf (boundedRow05 r) j / topsOf (boundedRow05 r) j := by
  change P2OriginalSaving19PrefixFirstMoment.encodedMoment _ _ 1 = _
  rw [P2OriginalSaving19PrefixFirstMoment.encoded_one _ _ (row_gap_nonneg r)
    (deviation_nonneg r j) (all_row_gaps r).1]
  exact firstMomentExpression_eq r j

theorem prefixMoment_one_range (r : Fin 56) (j : Fin 10) :
    prefixMoment r j 1 ∈ Set.Icc 0 (rangeTop r j) := by
  rw [prefixMoment_one]
  exact mean_deviation_bounds r j

#print axioms row_mean_bounds
#print axioms all_deviation_ranges
#print axioms mean_deviation_bounds
#print axioms firstMomentExpression_eq
#print axioms firstMomentExpression_range
#print axioms prefixMoment_zero
#print axioms prefixMoment_one
#print axioms prefixMoment_one_range

end
end ImbalancedChen.P2OriginalSaving19Cell05MomentBounds
