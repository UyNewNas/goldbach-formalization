# Durable handoff — P1.4 original Cell-indexed frozen archive sum

## Last verified recovery and immutable pins
Predecessor HEAD `aa144151be1eb36b2db027efef8d4ffaa10f4839` on `chatgpt/p1-full87-same-q-cell-ledger-20261109`, with previous full source, REPORT.md, REGISTRY.json, INPUT_BOUNDARY.md and HANDOFF.md read. This round's independent branch: `chatgpt/p1-full87-cell-indexed-archive-weight-20261109`. New Lean source commit `8c4c52f747ac374bc2c2f418dd5dccfd69c786c8` and proof packet `docs/source-only/20261109-full87-cell-indexed-archive-weight/`. The initial `9649ab3` is only historical navigation, never a reset point.

Fixed manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, constants c=`49044063/25000000`, K=`8452171/1250000`. No toolchain upgrade or manuscript version substitution.

## Changed files and Git blobs
- `P4AOriginalFull87CellIndexedArchiveWeight.lean`, 78 lines, Git blob `84a9eb79271e38b659da0b0e54f6ac62b19cf79e`; two public candidate theorem bodies, one private helper.
- `REPORT.md`, blob `8a3876c28a87685c2419bac0a1f1435e79ff06fd`.
- `INPUT_BOUNDARY.md`, blob `49de3fec539fdca2441a3d0d06d2c94d5bdfe1c1`.
- `REGISTRY.json`, blob `30c251f0eb669acd5c558a09025bb225b9c04e54`.
All four read back from exact branch matching Git blob SHAs. Handoff added in separate commit after the above source commit; use current branch HEAD from GitHub and do not reset to source commit.

## Exact in-paper candidate mathematics
Original `P4AOriginalFull87SourceDictionary.Cell` (87 genuine source constructors) has the PRE-EXISTING `globalIndex : Cell → Fin 87` and `globalIndex_bijective`, source blob `b35c77fc9f3905d87ceb9a3297625cb3267e795d`. Pre-existing `P4AOriginalFull87ArchiveSourceIndex.archivedRecordForOriginalCell`, blob `c7fa8c986b790d2ba09f6491c092b1c81563aeca`, maps each original Cell's index to the exact frozen numeric record, with seed conventions original ascending index 7 and original winner9 seed index 41, not numeric file ordinal. New lemma transports ANY rational Fin87 weight through this exact bijection to the original Cell sum. New helper transports 87-index Finset sum to the existing archive List sum. New public unweighted theorem states the exact six-stage frozen selected sum, `3111307568597708509491143/79228162514264337593543950336`, in the ORIGINAL `Cell` index rather than merely as a reordered List. No new dynamic parent or fake gain input.

Read frozen selected numeric JSON `verification/data/global-selected-numeric-completion-20261010.json` blob `34c8bb0facc3e24597c09d6b2e410e63c344ef5e`, and independent unequal/ascending blob `92edcac75bbcd22ec83690468c1dea12d3ced401` / `b5a4e188547835a6ffd7bab3f4d1649169058ec4`. Exact rational six-stage addition was checked and matches the registered sum; this does not inspect saved87 geometry or N-dependent physical occurrence.

## Actual checks and prohibitions
Static scan prohibited escapes absent, parenthesis/bracket balance 0. GitHub branch create/source commit/remote SHA readback confirmed. `lean --version`, `lake --version`, `elan --version`: exit 127 in the current execution environment; no exact pinned toolchain available. Hence SOURCE_ONLY / UNEVALUATED / UNCOMPILED, not KERNEL_REPLAYED, no transitive axioms audit, independent review, or actual saved87 geometry replay. No CI, Codex, connection to user's computer, additional compute, main/master modification, merge, force push, reserve spending or new axiom.

## Exact remaining math and next action
Missing saved87 physical geometry certificates/individual original witness bytes and actual N-dependent state/selected/remaining/actualParent/finiteCap mapping for all 87 Cells. A bijective archived LABEL map alone supplies none of original source membership or signed gain, and numerical gain cannot be transferred to a new tree by cap monotonicity. Next: recover authentic original witness bytes or regenerate their actual geometry checks against the original source dictionary, verify source membership/parent per Cell, and apply the exact archive-indexed weights ONLY after the real signed gain/integral identity is established.

Separately, once-pay same full-q first-disagreement stopped + five rank-eight frontier invoices against original legal integer PP X and H_N, preserve raw/finite/filtered and primitive/centre/modulus/endpoint corrections, ordinary integral, rank9 and changed/tagged, plus TWO separate compiler/density reserves. External manuscript §4 signed complete-rho_N PP AP input REGISTERED_NOT_PROVED / NOT_CALLED; prerequisites include original factorization, common phase, Gevrey, prime-product support and local corrections. No external theorem implemented. P1.4 parent YELLOW.
