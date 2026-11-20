# P3.5: exact original chart-level exceptional indexing

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`e54decd7b0da06dfcf44dab617b9d9d1e4d7c81f`. The containing commit is the
new SHA. Adds `Part3OriginalExceptionalChartIndex.lean` and this report
under `docs/source-only/20261120-p35-exceptional-chart-index/`. Lean
source SHA-256:
`4ddb3e25e67ce6fe6d29609899fd88afdce07b50c7f560ac8455e7e9f2a08f5f`.

## Exact proposed manuscript adaptation

The preceding packet bounded a finite sum over the sigma type whose
levels are the union of the original endpoint-corrected positive-integer
pieces. The trace source instead iterates over `chartLevels D k upper`.
This packet proposes an exact index bridge for that missing step:

1. `levels_image_eq_chart` says the image in N of the two-piece
   positive-level union is **exactly** `chartLevels D k upper`. Forward
   inclusion uses each piece's original chart filter; reverse inclusion
   uses the previously written `original_level_occurs` cover and the
   actual `levelCarrier_licensed` positivity proof.
2. `chartLevelEquiv` is a value-preserving bijection between the union's
   level subtype and the original trace chart-level subtype. The source
   reuses the exact actual level value and uses proof irrelevance only
   to identify positive-level witnesses; it does not collapse spectral
   multiplicities or add levels. Empty charts are included.
3. For each actual chart level, `chartSignedSlot` indexes the very same
   strict exceptional native basis. `chart_slot_positive` unfolds its
   false composite-sign branch to `nativeWeight * star(M)*N_raw`;
   `chart_slot_opposite` unfolds its true branch to
   `(8*kTransform) * star(M)*N_raw`, with the actual test and same native
   eigenindex in both. The choice depends on the original
   `traceNegative`, not just the separate Poisson sign.
4. `signed_sum_eq_original_chart_sum` reindexes the finite sigma sum
   exactly as an outer sum over the original `chartLevels` and an inner
   sum over the entire strict exceptional subtype at that same level.
   `signed_mode_eq_original_chart_sum` carries this equality through the
   preceding candidate's actual `actualCoeff`, physical `M sqrt Z`, and
   `chartY0` without changing their occurrences.

The proof is finite: filter membership and the existing original level
cover give the bijection; `Fintype.sum_sigma` followed by
`Fintype.sum_equiv` changes the order and indexing. It introduces no new
spectral bound, full-J assertion, new weight or hypothesis equivalent to
the target. It removes the **finite level-index identification** left
open by the preceding candidate, subject to eventual Lean verification.

This is not yet an equality with the complete original row spectrum:
splitting the original infinite cuspidal `tsum` into the strict finite
exceptional part and the remaining regular part is still required, as
are continuous/holomorphic pieces and the trace identities' sign and
summability hypotheses. In particular there is no claim that the full
G=H+M+E, (24), full J, ABL or all-cost 7/32 is completed.

## Sources and input boundary

* `Part3OriginalExceptionalJNativeCompletion.lean`, blob
  `a2f2a42763818451f4058d7354698611ebe04c43`, defines the strict
  exceptional family and provides `original_level_occurs` with the
  actual two printed interval endpoints.
* `Part3OriginalExceptionalPostRemovalPair.lean`, blob
  `a038900816ae4e167afb9f46ace2e142440d386c`, defines `levels` and
  `Slots`. The selected original `signedRawSlot` is from
  `Part3OriginalSignedExceptionalChart.lean`, blob
  `292f96931d23fb22545681824276ee576f468c51`; the original outer
  coefficient/chart scalar/test scale are in parent
  `Part3OriginalSignedExceptionalMode.lean`, blob
  `628b660ed173c0e1180b3eccb26b992017cdbbd3`.
* `Part3OriginalPrescribedChartSpectrum.lean`, blob
  `fc79ad8d2de109d661b52ba0e9bb83c3c8315e5a`, contains the actual trace
  `chartLevels` outer indexing; both raw sign branches are identified
  only at the finite term level here. The full `tsum` split is not
  assumed.
* Manuscript body at
  `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
  was rechecked: blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`,
  matching the chain; §7 (24) and §10(vii) in distribution blob
  `19f9672bc9b6d455045213c5e23e10433a9569d2` were reread. Pascadi v3 J,
  ABL v1 Lemmas 3.1–3.2, and numerical gap retain the exact registration
  and missing-supplier status of the prior chain; no new external input
  is added here.
* Pinned mathlib `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`
  at `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` was read to check the
  explicit `Fintype.sum_equiv` signature used in the proposed proof.

## Validation and next step

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including the finite equality proofs and parent chain. `command -v
lean` and `command -v lake` produced no executable path; the exact
import closure is not staged. No compiler was invoked, so no compiler
exit code or log exists. Source configuration reread: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions could not
be checked. Stack 8192 KiB, virtual memory unlimited, unchanged.
`sha256sum` gave the source hash above; `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). Neither is compilation. No CI was started.

Next stage and elaborate this exact import closure; kernel replay and
transitive-axiom audit remain pending. Prove the sign-specific finite
exceptional versus regular `tsum` decomposition and retain the original
continuous/holomorphic terms. Quantify both transform budgets, pay or
replace the raw n cost, and supply sharp J. The other chart/six-scale
aggregation, two zero lanes, actual cutoff tail, 14eta/28eta, 128C and
original N-threshold/reserve order remain separate obligations.
