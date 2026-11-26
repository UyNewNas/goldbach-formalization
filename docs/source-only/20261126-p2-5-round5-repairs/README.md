# P2 round5: six source candidates

These candidates address the six direct failures in the round4 normal stream
from task `381b23081efa4391a45337f2a1eb0ab8`, publication
`168973571f795dbe8fb1c1bccfd7f7c54899b36a`. All six saved preimages match that
publication byte for byte. Production sources remain unchanged.

The package is source-only. The completed round4 receipt and all six original
per-module logs have now been verified. They confirm 330 of 377 normal successes
and 41 of 69 accepted owned audits. The six original logs contain exactly the
21 reviewed diagnostics. Current-context acceptance of these repairs and the
future compile outcome remain unverified.

## Selected changes

| Module | Change | Source reuse |
| --- | --- | --- |
| `P4AOriginalFull87SourceDictionary` | Three diagnosed unnecessary sequence-focus operators become ordinary sequencing. | Preserve the current split definitions/imports; the older P15 monolithic source would undo that extraction. |
| `P4AOriginalH5H7SourceDispatch` | Two diagnosed sequence-focus tails become sequential tactics within each `all_goals` invocation. | Preserve all round4 simp-list repairs. The older batch83 source would reintroduce rejected arguments. |
| `P2OriginalFourthCapProducerInterface` | Two sequence-focus cleanups, two unreachable `ring` tails removed, and one no-op simp step removed after all four arguments were diagnosed unused. | Preserve the complete batch39 mathematical repair already installed in round4. |
| `P1OriginalHistoricalRetainedModulusLevel` | Supply the existing `h4` argument at two calls. | Exact historical batch57 source; its baseline equals the current source. |
| `P1OriginalCoarseFourthCellLimit` | Use `setIntegral_empty` and unfold the applied integrand lambdas with `dsimp only` before rewriting. | Exact historical batch41 source; its baseline equals the current source. |
| `P4AActualEighthInheritedHistoryGuard` | Three diagnosed unnecessary sequence-focus operators become sequential tactics. | Preserve the historical batch80 mathematical repair already installed in round4. |

The retained-modulus repair adds no hypothesis. The existing theorem already
obtains `he`, `hTheta`, `h4`, and `h5` from `originalCeilingCheck_sound` and its
existing `hc` premise. Its called fourth-level theorem explicitly expects `h4`
before `N`; the two call sites had omitted that available proof.

## Historical evidence and its limits

Both reused sources have historical normal and independent kernel exits zero.
The saved before/after source identities were checked against the historical
source snapshots, and the complete normal, kernel, and audit log hashes were
verified. Compressed exact logs and small receipts are preserved under
`historical/` with their original and stored hashes in `SOURCE_SELECTION.json`.

Batch41 checked all 28 environment-public declarations of its target. Batch57
checked all 53 environment-owned declarations of its target, including private
and generated declarations. These scopes are recorded separately. Neither
historical result establishes acceptance under the current P2 dependency and
linter context, and no historical objects were transferred.

## Preservation and next validation

Static checks preserve every theorem header, every non-theorem command, imports,
and source option lines. No linter setting is changed and no axiom, `sorry`,
`admit`, `native_decide`, `unsafe`, or kernel-check bypass is added. The five
round4 new normal successes remain byte-identical to the selected round4
sources and are excluded from this patch.

`REPAIRS.patch` is reviewable against the current production tree; `before/`
and `after/` contain the exact six-file comparison. `STATIC_VERIFICATION.json`
records static checks only. Current-context Lean validation is still pending.
The prepared round5 runner retains the unchanged 377-module closure and 69
owned audit targets and reuses only objects qualified by the original
source/dependency checks. Eight local guard tests use the actual prior receipt
and resolve all 377 source files at the prior Git commit, including 15 symlink
entries. See `RESUME_PLAN.md` and `WRAPPER_TESTS.log`; no Lean or cloud job has
been executed for round5.
