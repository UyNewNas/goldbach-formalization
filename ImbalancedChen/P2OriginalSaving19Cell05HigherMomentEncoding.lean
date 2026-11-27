import ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ96RecordChecks

/-! Connect the unchanged encoded prefix table to the original rational
moment formula, using only proved encodings of the actual coordinates.
This candidate does not assume a stored moment or an integral conclusion. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05HigherMomentEncoding
noncomputable section
open P2OriginalSaving19NonnegativeRationalEncoding
open P2OriginalSaving19PrefixFirstMoment
open P2OriginalSaving19HigherMomentsPrefix
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19Cell05GeometryCertificate
open P2OriginalSaving19Cell05MomentBounds

theorem encoded_eq_rationalMoment (gaps deviations : Fin 9 → ℚ)
    (hg : ∀ i, 0 ≤ gaps i) (hy : ∀ i, 0 ≤ deviations i)
    (k : ℕ) (hk : k ≤ 6) :
    encodedMoment gaps deviations k =
      P2OriginalSaving19HigherMoments.rationalMoment gaps deviations k := by
  exact normalizedMoment_eq_encoded
    (numerator gaps) (numerator deviations) (denominator deviations) (denominator gaps) k
    (denominator_pos deviations).ne' (denominator_pos gaps).ne' hk
    gaps deviations (encoding gaps hg) (encoding deviations hy)

theorem all_prefix_moments (r : Fin 56) (j : Fin 10) (k : ℕ) (hk : k ≤ 6) :
    prefixMoment r j k =
      P2OriginalSaving19HigherMoments.rationalMoment
        (fun i => gapQ (boundedRowVertex05 r i)) (deviation r j) k :=
  encoded_eq_rationalMoment _ _ (row_gap_nonneg r) (deviation_nonneg r j) k hk

#print axioms encoded_eq_rationalMoment
#print axioms all_prefix_moments

end
end ImbalancedChen.P2OriginalSaving19Cell05HigherMomentEncoding
