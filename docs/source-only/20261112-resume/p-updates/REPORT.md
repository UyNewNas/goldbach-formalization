# P1–P5 source update inventory (2026-11-12)

## Scope and result

This inventory reconciles the five requested P lines against the **2026-11-10 frozen local tracker** (`goldbach-proof-github-sources-20261110/SOURCE_INDEX.json` plus `PUBLICATION_SOURCE_INDEX.json`). It is a bounded P1–P5 source-only inventory, not a census of all 290 remote heads or the full publication delta. The scan covered all selected P1 source package branches, the P3/P5 source chains, and the exact P2/P4 candidate commits.

There are 69 source records: 67 newly introduced, distinct Lean paths/blobs; one existing Lean module modified in P2; and one P3 path/blob already present in the Nov 10 archive. The full module paths, source commit SHA, Git blob, raw SHA-256, line count, and direct imports are in `INDEX.json`. No Lean files were copied into a second source tree.

| Line | Current requested head | Source commit(s) represented | Lean records | Status boundary |
|---|---|---|---:|---|
| P1 | `a023ae055d3d90738f6965a2848266aa13089faf` (`chatgpt/p1-full87-sixth-both-zero-invoice-20261112`) | 19 package directories across current P1 heads; invoice source last updated at `544e3b07a5572a2ae21bad180e48e1cdccd91c91` | 21 | SOURCE_ONLY; uncompiled, P1.4 open |
| P2 | `d44b83e057a538f58791fc9eb6a8e8acfef58b25` (`chatgpt/p2-integral-rounding-20261111`) | `58e36e0a0ece9c5e9a869294fb87bcaf92ff7441` | 2 | SOURCE_ONLY_UNCOMPILED; one added checker and one modified ledger |
| P3 | `a29bd6b4cba6d1b7e8cd48165f3a0f76f040082b` (`chatgpt/p3-internal-original-w-20261105`) | P3 additions in shared package `docs/source-only/20261105-p3-fourier-coordinate-ibp/`, through `8d15f31906ae8a108336bedb3d0c4b692812a4cb` | 21 | SOURCE_ONLY_UNCOMPILED; P3.6 open |
| P4 | `eea9486f7b101d484e2938e97499c1d77cc1a67a` (`chatgpt/p4-uniform-correction-20261111`) | `74cc368ce01532d78b62f064b11979c01e26266b` plus predecessor P4 additions | 6 | SOURCE_ONLY_UNCOMPILED; full hUpper open |
| P5 | `001d139e667eb5cb42f1e9ca8f02de221b00db5c` (`chatgpt/p5-h34-full-tagged-actual-fin-20261112`) | P5 h34 source chain through `547e997645225e528d8d34a75cb5305ecee87c9b` | 19 | PARTIAL_SOURCE_INCREMENT; full h34 open |

P1 is intentionally multi-branch: the primary invoice head above does not stand in for the other P1 package heads. The 21 Lean records span the 19 Nov 11–12 full87 package directories listed in `INDEX.json`. For P5, the latest source is the U4 actual-Fin double-tag module at commit `547e997645225e528d8d34a75cb5305ecee87c9b`; `001d139…` is the later registry/remote-comparison update. Its documented predecessor chain includes `3f9af8f80deca05a0d06fbfdb6d690ad740bd2e5`, `916583147ec9ce90b22cc8c5d8022a2428ce85b9`, and `2c03bf4db09133f46735b6ddfda0661dda41eba5`.

## Exact archive overlap and package clues

The archived Nov 10 indexes contain 942 file records. One P3 source has an exact same-path, same-blob hit: `P3HBSmoothLogFiniteDerivatives.lean`, blob `5e7547531d44d2091b3eddd39ac11cace74db2fe`. It is included as a provenance/branch-diff clue, not counted as a newly unique source. There were no other same-path or same-basename matches in those archived indexes. The updated P1 invoice module has distinct earlier and current versions: initial source commit `4b621986e2c0717d76fc9cdc63845d65653059ee`, current source commit `544e3b07a5572a2ae21bad180e48e1cdccd91c91`, current blob `fe848722381b301e3d044a284aad29cb4fa1909e`. P2's existing `P2HybridThirdChargeLedger.lean` is a deliberate same-path replacement: old blob `53d2293e0a560006166fd04d6fc2ac002a73d03c`, new blob `26212bccc0c47c78e571663d05b31f525a72f1e3`.

These are deterministic identity comparisons against the archived tracker. They do not prove that every unindexed local draft was published or absent; `sourceonly-drafts` contains no matching candidate module names.

## Verification boundary

All five requested heads are source/handoff/registry evidence only. `SOURCE_ONLY`, `SOURCE_ONLY_UNCOMPILED`, and `PARTIAL_SOURCE_INCREMENT` are preserved in the index; none is interpreted as CI success, Lean elaboration, kernel replay, axiom audit, or mathematical closure. The corresponding commits are `[skip ci]` or explicitly decline CI dispatch. No local Lean, Lake, LSP, guard, numerical proof, or CI was run for this inventory. Mathematical closure remains with the review agent.
