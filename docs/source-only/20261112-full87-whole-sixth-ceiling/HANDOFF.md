# Durable handoff — original fifth + whole sixth scalar ceiling

Task branch `chatgpt/p1-full87-original-fifth-global-ceiling-20261112` created from **verified** `05e8685f2c069867017f9d14b725ca8910bfbe7d`. Current candidate source `docs/source-only/20261112-full87-whole-sixth-ceiling/P4AOriginalFull87WholeSixthCeiling.lean`, blob `3e0236a913e9f52847d6a090f12cace1020b23e9`. **Read live HEAD and REGISTRY before any next continuation.** The old SHA `9649ab3` is not a reset target.

Advance: prove at source-candidate level the actual constructor `originalSeed,fallbackSeed,lambda3,exponent4,exponent5,actualParent5` all ≤299/500, finite `cap5≤299/500`, raw complete `currentSixthExponent≤299/500` and active/inactive literal `level6Exponent≤299/500` on every history. Original selected masks, old guards, original finiteMax seeds, chrono stage order, one quantizer clamp and no occurrence deduplication are retained.

Caution: `299/500-153/256=11/32000`; previous 153/256 strict-action cap CANNOT globally cover inherited fifth or raw third-inactive histories. Earliest source commit `8e0507c` contained a faulty monotone rounding comparison; `c6644bf` corrected it with the real `clamp_bounds` and `downCap_error`. No kernel credit even after this correction.

Next source locations, already read this round:
1. `docs/source-only/20261112-full87-licensed-sixth-ceiling/P4AOriginalFull87LicensedSixthCeiling.lean`
2. `docs/source-only/20261104-full87-licensed-sixth/P4AOriginalFull87LicensedSixthPolicy.lean`
3. `docs/source-only/20261103-full87-finite-parent/P4AOriginalFull87FiniteParentCaps.lean`
4. `ImbalancedChen/P1OriginalHistoricalRetainedModulusLevel.lean` (different old fifth policy; its table certificate must NOT be transplanted automatically)
5. `docs/source-only/20261107-full87-retained-terminal-ceiling/P4AOriginalFull87RetainedTerminalCeiling.lean` (actual terminal product recursion, not a PP proof)
6. `ImbalancedChen/P4AActualSixthFrozenEighthAdmission.lean` if available in fixed pin, for actual rank-six retained validity.

Next proof MUST show actual first-exit retained rough *leaf* bound (including fifth inherited and third-inactive paths and rank-eight own selected/carry branches); only then combine with actual small Rosser factor L and establish complete modulus PP level `ab<N^theta`, fixed theta<1. Do not use `prod(roughPrimeUniverse)` as fake N^theta or claim monotonicity of signed saving.

Frozen manuscript 9731290e blob d529bea2; Lean v4.33.0-rc1, mathlib e4c91783, native 09b97db; c=49044063/25000000, K=8452171/1250000. External §4 sharp PP registered but NOT PROVED / NOT CALLED. 10,000/10,000 Fraction synthetic checks; no original87 arithmetic replay. `lean/lake/elan --version` all exit127, .lake deps missing. SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no kernel replay, transitive axiom audit, independent review or CI. No other task branch touched.
