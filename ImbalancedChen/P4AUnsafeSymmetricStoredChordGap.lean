import ImbalancedChen.P4AUnsafeSymmetricChordGap
import ImbalancedChen.P4AOriginalStoredQueryStrictComparison

/-! SOURCEONLY / UNCOMPILED / OPEN30.
Same immutable-reader adapter. Strictness remains conditional on the displayed
canonical gap/interval width comparison; that quantitative inequality is OPEN. -/
namespace ImbalancedChen.OriginalThirdP4AUnsafeSymmetricStoredChordGapSourceOnly

noncomputable section
open MeasureTheory
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalU2StoredQueryLookupSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdP4AUnsafeSymmetricChordGapSourceOnly
open P4AOriginalStoredQueryStrictComparison20261024zSourceOnly

/-- No query-order premise is needed for the corrected actual OLD bound. -/
theorem witness_stored_corrected_chord_le_actual_integral (T : CheckedBlockTable) :
    tentOldChord .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024))
        (queryLo T witnessLow) (queryLo T witnessHigh)-
      witnessChordGap (queryLo T witnessLow) (queryLo T witnessHigh) ≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p)
        ∂prismProbability (21/128) (169/1024) (1/32) (33/1024) := by
  exact witness_corrected_chord_le_actual_integral _ _
    (witness_intervals_sound T).1.1 (witness_intervals_sound T).2.1

theorem witness_stored_gap_pos_of_canonical_gap_gt_width (T : CheckedBlockTable)
    (hgap : queryWidth T witnessHigh <
      actualExtendedThirdLowerFactor (61/8:ℝ)-
        actualExtendedThirdLowerFactor (238/33:ℝ)) :
    0 < witnessChordGap (queryLo T witnessLow) (queryLo T witnessHigh) := by
  have hi := witness_strict_lower_queries_of_gap_gt_width T hgap
  have hq : queryLo T witnessLow < queryLo T witnessHigh := value_strict_mono hi
  exact witnessChordGap_pos hq

/-- The strict mean discrepancy is closed. The remaining condition is the
same-reader quantitative query comparison, with no saved bound conclusion. -/
theorem witness_stored_ordered_chord_lt_producer_of_canonical_gap_gt_width
    (T : CheckedBlockTable)
    (hgap : queryWidth T witnessHigh <
      actualExtendedThirdLowerFactor (61/8:ℝ)-
        actualExtendedThirdLowerFactor (238/33:ℝ)) :
    orderedTentChord .xz .fall (21/128) (169/1024) (1/32) (33/1024)
        (queryLo T witnessLow) (queryLo T witnessHigh) <
      tentOldChord .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024))
        (queryLo T witnessLow) (queryLo T witnessHigh) := by
  apply witness_ordered_chord_lt_producer_of_query_lt
  exact value_strict_mono (witness_strict_lower_queries_of_gap_gt_width T hgap)

end
end ImbalancedChen.OriginalThirdP4AUnsafeSymmetricStoredChordGapSourceOnly
