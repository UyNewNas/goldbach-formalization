# Saving19 moment prefix evaluator reuse

The existing `P2Winner9HomogeneousRecurrence.prefixCoefficients` and its correctness theorem are reused byte for byte. This package adds only the interface to the unchanged Saving19 homogeneous convolution and a source candidate connecting the result to `authorMoment` and `rationalMoment`. It introduces no analytic estimate or saved numerical assumption.

## Verified locally

`PrefixInterface` proves the cast of the existing coefficient table equals any coefficient function satisfying the original empty/cons equations. `PrefixMoments` computes the weighted numerator with one degree-0..6 table and proves its exact rational convolution formula. Both new owners passed normal compilation and independent `leanchecker` under the unchanged 4 GiB / 180 s / one-thread diagnostic bounds. Printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`. This is local diagnostic evidence, not the P1 all-owned acceptance pipeline.

The retained Winner9 source was not edited or re-proved. No accessible local object for that import was found; its exact 8,441-byte source was compiled once solely to make the existing supplier available in this isolated diagnostic environment. That setup is not counted as a new formalization result. No analytic dependency closure was rebuilt.

The first interface attempt had two elaboration errors: a polymorphic base case required simplification, and a `Fin` sum conversion needed its explicit function. The failed source/log remain under `attempts/interface-v1` and `logs`; it produced no accepted object. The corrected source alone received normal/kernel success.

## Still source-only

`HigherMomentsPrefix` has three specialized theorems: exact equality to `authorMoment`, exact equality to the original common-denominator `rationalMoment`, and transport from nine original rational coordinates with explicit integer encodings. The `completeH` empty/cons interface is discharged with its original defining equations. The final theorem requires only nonzero common denominators and exact coordinate identities; it does not assume moments, saved floors, geometry, ownership, or the endpoint. This module has been independently reviewed but has not been compiled against the real P1 facade.

The nonnegative integer input type does not license truncation of a negative original coordinate. Each actual row must still supply genuine exact gap/deviation encodings, and every requested degree must satisfy `k ≤ 6`. No actual 28,918-row array, Q80/Q96 floor, or aggregate total has been checked by this package.

## Manuscript boundary

The pinned 2026-11-06 appendix gives the barycentric simplex moment formula at `num:simplex-moment` (source commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`). It does not print these Newton/prefix representation identities as separate theorems. This package is the necessary finite-algebra evaluation interface for that manuscript calculation, reusing an existing project evaluator. It adds no manuscript-external estimate.

See `SOURCE_MANIFEST.json` for exact source, object, receipt, budget, and independent-review fingerprints. The production facade and all accepted structural moment suppliers remain unchanged.
