# P5.6 / h34 — strictly positive D5 and D7 actual integrals

Date: 2026-11-19.
Baseline: 068ee092cc40ee800a9af5f4a3384afff372d6dd.
Branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d.
Status: PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

## New manuscript-internal mathematics

The candidate source Part5OriginalH430D5D7PositiveRationalLower.lean proves a new
strictly positive lower for EACH of the two previously unquantified original
W2 terms. D5 preserves the exact three-affine support and its physical cap
10/29. An interior segment [117/454, 3/10] in the ORIGINAL second affine
piece has log argument >=5/4 and slice >=22/25. Its exact width times
22/25 is 1056/28375 >37/1000. The other two portions are explicitly
nonnegative, giving d5Logs >=37/1000 as a candidate.

D7 preserves the literal max(u,1-16u/5) lower support, weak support wall,
and full [1265/5648,100/353] outer interval. An original second-affine
subsegment [5/21,1/4] has log argument >=6/5 and slice >=18/25. The
exact Darboux mass is 3/350 >1/125. The original first piece and trailing
second segment are nonnegative, giving d7Log >=1/125 as a candidate.

Both arguments consume existing Mathlib-backed RationalLogCertificate
soundness for two-term rational lower series and actual outer-integral
continuity/additivity. All endpoints, support domains and normalisation
are unchanged. No float is used as a premise.

With the previous original singleton 0.057+0.005+0.029, D6 0.11 and
D8 0.04, the candidate seven-piece coefficient improves from
lambda>=241/5000 to lambda>=143/2500=0.0572. This is STILL below 0.13.
The new coefficient is NOT the seed/payment theorem and does not pay
the fixed 20249/1000000 analytic intercept.

## Remaining manuscript-internal obligations

- Compile this candidate source and pinned import closure; inspect proof
  elaboration and kernel dependencies. No compilation is asserted.
- Obtain enough genuine seven-domain lower mass for lambda>=13/100,
  if the frozen coefficient actually permits it. Investigate exact
  values before any unproductive fine parameter tweaking.
- Pay fixed analytic intercept from true original counts and prove
  both Q80 seed table inequalities for the frozen F.
- Complete true 430-round retention/Buchstab/bank CLOSED-CELL induction,
  original U3/U4 full/selected/inherited counts, root norm 7/2,
  owner rejection lanes, native histories, PP/same-rho, integral--Theta--count,
  and one nested causal 430+11 refinement.
- Kernel replay, transitive axiom audit, finite certification and
  downstream compiled closure are UNEVALUATED.

No P1.4/P3.6, original c/K, row norm 12, true alpha, same Q,
source thresholds, toolchain, dependencies or CI configuration are changed.

## Execution and validation

GitHub connector reads of starting REPORT/REGISTRY/EXTERNAL_INPUTS, latest
branch ref, directly relevant pinned Lean sources and geometry are complete.
Branch permission was confirmed admin. A shell check found no lean/lake/elan,
and direct git HTTPS failed DNS; source-only files are not installed as a
buildable ImbalancedChen import closure. The GitHub connector exposes no
workflow-dispatch action for a targeted Lean build. Therefore native
Lean/Lake compilation, kernel replay, axiom audit, finite proof checks and
CI execution for the new module remain UNCOMPILED / UNEVALUATED. Arithmetic
identities were independently checked with exact rational fractions, not
claimed as formal Lean evidence.

Next precise action: seek actual toolchain/import-closure compilation;
then certify additional true D5/D7/other-domain mass only when justified
by the frozen integral and follow the source-count payment path.
