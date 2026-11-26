# Explicit selection of the two existing pending source candidates

This addendum records root's subsequent explicit source selection under
`SUCCESSOR_PLAN.md`, Task 1. The original plan remains unchanged.

After the complete actual v8 export was available, root independently reviewed
the four full `Eq.subst` motives in the existing Arithmetic and SourceFacts
candidates and selected them for the new attempt. Their original actual owners
remain `PENDING`, with empty stage dictionaries and no accepted object. No failure
of either owner is asserted, and no performance improvement has been proved.

The exact selection and source review is
`docs/source-only/20261126-p2-5-cell00-floors-transport/optional-pending-consumers/ROOT_SELECTED_SOURCE_REVIEW.json`,
7,804 B, SHA256
`1f74d16efda89450c01d58a7fa2a75092e7a13fab01eef33d0d4c777e121f4f2`.
Both candidates already existed in publication
`b86f5fb7421a4a153b2530fa3aa1993521b39192`; this successor does not rewrite them.

| Module suffix | Selected source SHA256 |
| --- | --- |
| OriginalArithmetic | `70363c3b1f704889b3b6e68086cb4439170e01e810d6496b7ffe4e66d24ae24f` |
| OriginalSourceFacts | `ca682b04d22c87d47f6adb205e8b7da5074da3074cafd4157f916297336607a7` |

`select_pending_source_overlays` applies only these two rows after the unchanged
Floors selector. It binds their exact old/new source identities, original
pending status, unchanged imports/public interfaces, and absence of new
assumptions or private helpers. It requires precisely the three fresh consumer
rows to differ from the actual v8 source graph and all other 42 rows to remain
equal. An extra overlay, an accepted-owner target, changed imports/public names,
wrong SHA or an invented prior failure is rejected.

The consumer order, 42 accepted dependencies, 45-module graph, nine new stages,
all historical evidence checks and every normal/kernel/full-owned gate remain
the same. Original v8, historical candidate observations, old receipts and all
accepted proof sources remain unchanged.

The one new boundary test first failed because the exact overlay helper did not
yet exist. Its first implemented run exposed a test-fixture assumption that all
legacy source rows had `public_namespace`; the test was corrected to compare
optional fields while its complete 42-row equality check remained. The final
actual-evidence test group passed all five tests, including seven new overlay
rejection cases and eleven actual-metadata rejection cases. No Lean or remote
execution occurred during this work.
