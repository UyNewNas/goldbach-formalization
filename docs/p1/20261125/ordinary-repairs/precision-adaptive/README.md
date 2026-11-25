# Ordinary Precision / Adaptive proof-expression repairs

Status: source candidates only. Actual normal, kernel and full-owned verification remains pending under root's existing guarded queue.

## Actual failures and complete evidence

The first ordinary-five task `job_daf12bb5479e473b9dcc398a3e3953eb` failed all five target normal builds at source `220c14630ffd266f824bdbf0977147ecb740c0dd`. This directory owns only `P4BCompactSmoothMassPrecision` (three errors, 12.21523972399882 s) and `P2OriginalAdaptiveSourceSplit` (two errors, 6.325086949998877 s).

Read-only inspection `job_24839c416962474b8b35c9c6f4adab18` read the existing target logs and normal-command records. It succeeded in 0.07124924659729004 s with exit 0. Its complete 20,892-byte output was downloaded through EOF, with `output_truncated=false`; the embedded base64 decoded to exactly the reported bytes and text. The output SHA256 is `85fe1b10de91e12b90d40c8acaed7d9aef2ea10578a85afc39a8011c66fd9e63`.

`REPAIRS.json` embeds all five complete error sections for these two owners and their exact failed commands/log hashes. It also records the scratch path of the original five-target inspection output. The scratch payload is not claimed to be included in Git. No compilation was repeated to obtain these diagnostics.

## Four proof-expression changes

| Owner / original line | Actual cause | Candidate change |
|---|---|---|
| Precision 92 | `Finset.not_mem_empty` is unavailable. | Close contradictory empty-set membership with `simp at hx`. |
| Precision 105–106 | The `rfl` branch removes `x`; the actual remaining binder is `y`. The unknown identifier causes the subsequent arithmetic failure. | Use `hspan y`; retain the existing two-inequality `linarith` proof. |
| Adaptive 53 | Rewriting the `ite` condition leaves a dependent `Decidable` argument with the old type. | Use `simp only` with the same exact rational/cross-product equivalence. |
| Adaptive 131 | The rewrite pattern expects the expanded closed domain, while the goal contains `rootCell`. | Explicitly instantiate the existing integer-box dictionary, then simplify with the unchanged integer-leaf equality. |

All 12 theorem declarations (11 public and one private), all eight definitions, every import and every option remain byte-identical to source220. A byte-level check confirms that the candidates equal the pinned preimages plus exactly these four proof replacements. `git diff --check` passed. No axiom, `sorry`, `admit`, `native_decide`, altered hypothesis, narrower finite range, or weakened geometric condition was added.

## Manuscript and reliable reuse

The pinned 20261106 manuscript's `argument.tex`, equation `eq:current-bad-mass`, identifies the exact coefficient as `log(1/b)` and explains positive smooth approximation. The existing Precision proof takes a finite subcover and combines the already accepted two-endpoint estimates; it introduces no uniform PNT premise. `coefficient-appendix.tex`, “Individual sharp intervals,” supplies the surrounding positive-strip approximation discussion.

The numerical appendix's directed arithmetic and compact-third partition discussion remains the mathematical context for Adaptive. The unchanged definitions preserve the strict cross-product axis comparison, incumbent-on-ties behavior, integer midpoint, raw coordinates, left/right emission order and all closed-domain portions. The manuscript passage does not itself specify the full producer heap trace. No producer script was found in the examined local scratch inventory, and this expression repair does not claim to reconstruct or newly verify that trace.

Both immediate parents already have full-owned acceptance: `P4BSmoothMassParameterOrder` in Batch10 chunk008/lane0 (nine owned/public declarations) and `P2OriginalInitialClosedTree` in chunk001/lane0 (24 owned/public declarations). `REPAIRS.json` pins the exact archive, receipt members and source hashes. The generic closed-tree dictionary is reused from the existing imported dependency context; `P2OriginalAdaptiveForestSourceIdentity` provides an explicit dictionary-application source exemplar, without any additional acceptance claim for that exemplar.

## Frozen candidates

| Module | Before SHA256 | Candidate SHA256 |
|---|---|---|
| `P4BCompactSmoothMassPrecision` | `8918c971270bdb87001eae05c7d4fc8693b68e4b15cf1383b6d92f078aeedbae` | `26ecc651116b3b9b61e6d77e24d67343b28bbaf43f014abfe5097b2761e322d9` |
| `P2OriginalAdaptiveSourceSplit` | `3a7efb58c997e7a65b0d536cf4534868abd5ff109885ca31383f679687ae18cf` | `adbcc11b297d4794b8174f82624e283ec708f49e32230c01d308e7e5f5d98df1` |

No Lean/Lake compilation, source installation, resource change, staging or commit was performed by this repair task. Root owns publication and fresh normal/kernel/full-owned verification; the unchanged accepted parents are to be reused.
