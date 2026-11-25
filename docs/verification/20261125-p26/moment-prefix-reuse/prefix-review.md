# Saving19 prefix interface: independent source review

No semantic obstruction or hidden final-conclusion hypothesis was found in the three reviewed sources. This is a read-only review; it is not a compilation or production acceptance.

## Reviewed sources

- `ImbalancedChen.P2OriginalSaving19PrefixInterface` — SHA256 `7372895eef413da4baf0e67fb1986a18ab9d9b4d31e614c676dcaaac1f216413`; reported local normal/kernel passed; independent read-only review.
- `ImbalancedChen.P2OriginalSaving19PrefixMoments` — SHA256 `f9ae192da924c00e516979dc77317ae543032949643fd2f1e2196c0a6f636e3b`; normal passed and kernel pending at review request; independent read-only review.
- `ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix` — SHA256 `714b2e83b9e09d6881da59b8c63c287ae48fb22e7d74431b1da186c9fa427c34`; SOURCE_ONLY; not compiled.
- `ImbalancedChen.P2Winner9HomogeneousRecurrence` — SHA256 `4234d0ccf486c9d53f13bee20a2a48b1751edd572fcbbb7b6cf057169803591d`; unchanged reused supplier.

## Findings

- The generic coefficient interface assumes only the exact empty/cons equations. The Saving19 specialization discharges both with the original completeH defining equations (rfl).
- Every used coefficient has index k-j.val <= k <= 6. No degree-seven coefficient or extra degree assumption is introduced.
- The weighted Nat numerator casts exactly to the finite weighted convolution. Its denominator is (sum g)*choose(9+k,k)*d^k, with no dropped factor or term.
- The author bridge matches the original authorMoment definition and uses the original authorMoment_eq_rationalMoment only under k<=6.
- The rational common denominator bridge uses only d!=0 and the existing rationalMoment_common_denominator. The gap scale bridge uses s!=0 and the existing rationalMoment_gap_scale with scale s inverse.
- The encoded theorem has all nine exact coordinate hypotheses hg/hz. Nat g,z explicitly restrict this representation to nonnegative arrays; no signed deviation is truncated or implicitly coerced to Nat.
- There is no moment, floor, geometry, ownership, or final conclusion hypothesis. Even sum(g)=0 is allowed algebraically by the original total rational division semantics; later positivity or lower-bound arguments remain separate.

## Limits

- No compilation or source modification performed in this independent review.
- HigherMomentsPrefix remains SOURCE_ONLY, not accepted or compiled.
- The actual original row arrays have not been bound to g,z,d,s here; closed coordinate proofs hg/hz and denominator nonzero certificates remain required.
- The review does not establish any numerical floor or final theorem.

## API comparison

The comparison used `/workspace/p26-recovery-candidates/moment-facade/ImbalancedChen/P2OriginalSaving19HigherMoments.lean` for the exact author/rational moment definitions and denominator/scale theorems, and `/workspace/p26-recovery-candidates/moments/ImbalancedChen/P2OriginalSaving19HigherMomentsCore.lean` for completeH. The original unchanged recurrence supplier was inspected for prefixCoefficients and prefixCoefficients_correct.
