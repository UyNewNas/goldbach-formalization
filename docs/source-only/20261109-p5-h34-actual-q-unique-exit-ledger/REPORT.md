# P5.6 → h34: one real signed first-excluded history per distinct actual (Q,p,ell)

Date: 2026-11-09 UTC.
Branch: `chatgpt/p5-h34-actual-q-unique-exit-ledger-20261109`.
**Verified parent baseline:** `8b7e4d5e554e315f37a43b3718c3a3207c87c700`, continuing the previous actual-Q original-receipt first-exit packet. Earlier historical entry `0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0` was read but not used as working baseline.

Mathematical source commits: `d036de3f333ed87f281f667d0d8a6eabec4a9dd7` (first source) and `5b24562bbe61cc6cc13cd1ce35385103db9d044c` (cardinal q/tag collision overhang).
Source: `Part5OriginalH430ActualQUniqueExitLedger.lean`, 240 lines, four definitions and **nine** candidate theorem declarations, final GitHub blob `5a9b2e546f140721b308370c233ded4c3a252e31`.

**PARTIAL_SOURCE_INCREMENT · SOURCE_ONLY · UNCOMPILED · UNEVALUATED · FULL_H34_OPEN.**

## New manuscript-internal argument

The previous packet supplied a true first-excluded signed witness **for each original q/tag receipt** separately at its physical Q. Its own report warned that q- and U3/U4-tag collisions can project to the same event. Counting each witness as a separately payable event would multiply an actual historical position incorrectly.

This packet builds one finite index of triples `(originalPhysicalQ,(arithmetic p,first forbidden ell))` across BOTH different original frozen-failure and frozen-rejected sets. The two sets are actually disjoint as receipts, while their image keys need not be. The bad-prime rule is the frozen N^a cutoff on the former, and the frozen-root-cutoff rule on the latter. The physical Q remains tag/p-dependent. Different q receipts are retained in their **full finite fibres**.

Nine candidate theorems prove:

1. Exact original receipt fibre membership and agreement of each fibre member with the indexed physical Q.
2. Reindexing of any original additive signed q/tag weight by real physical event keys, and exact cardinality reindexing; no key injectivity is assumed.
3. Nonempty original receipt witness for each enumerated physical key, plus the natural-number identity
   `#original receipts = #distinct actual (Q,p,ell) keys + sum_{key}(#receipts in key fibre - 1)`.
   The overhang is an unpaid multiplicity, not a guessed payment.
4. Exact two-source signed split, preserving both different rejection causes.
5. For every enumerated physical key and actual `z0 ≤ cap`, use the corresponding original witness to produce **exactly one** rank-two event with prefix `[ell,p]`, positive bare event mass, and its real **negative** signed exit times the complete remaining Euler product.
6. Exact real-q-weight identity, with the signed history term booked **once per distinct actual (Q,p,ell) key**, and all q/tag source minus that signed history explicitly carried as a separate residual.

In symbols, for `K` the actual triple-image and `F_k` its original q/tag fibre, the main identity is:

`sum_{z in frozen-fail} w(z) + sum_{z in rejected-fail} w(z)
 = sum_{k in K} E_signed(k) + sum_{k in K} (sum_{z in F_k} w(z) - E_signed(k))`.

There is **no bound on the residual**, no claim that a single Euler event can pay every receipt, no equality between U3 and U4 physical Q, and no assertion that those unique keys are full/selected/inherited history owners. The result is mathematically a correct kind of finite source-accounting candidate, not h34 closure.

## Frozen scope

- Manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- No new PNT/Mertens/BV, target-equivalent assumption, custom axiom, sorry/admit, unsafe/native proof escape, or change to c/K, root 7/2, row 12, actual alpha, parameter Q, root norms or numerical430 inputs.
- No changes to production sources, P1.4, P3.6, existing h34 packets, CI, workflow settings, toolchains or master; unique branch and unique source-only packet folder.

## Validation and exact boundaries

- GitHub connector confirmed account `UyNewNas` has push permission. Parent branch `chatgpt/p5-h34-actual-q-first-exit-receipts-20261109` was at `8b7e4d5`; the new branch was created **from that exact SHA**.
- The current environment has `git` but no `lean`, `lake`, or `elan` binary; git ls-remote to GitHub failed with DNS `Could not resolve host: github.com`. The source-only imports have not been staged as `ImbalancedChen` modules at the pinned versions. The authorized targeted compilation could therefore not be run here; there was no successful Lean elaboration or local Lake build.
- Textual forbidden-token checks and actual GitHub blob readback were performed, but they are NOT Lean parsing, elaboration, compiler success, kernel replay, transitive axiom audit, or independent proof review.
- No existing CI configuration was changed; no CI dispatch, kernel replay, transitive axiom audit or finite 430 replay was performed. No green status is awarded. All inherited source-only finite guards remain UNEVALUATED.

## Actual next proof obligations

1. Identify the original **full/selected/inherited** owner and stage for the key's physical `Q,p,ell`; prove one historical event's actual signed and capacity contribution under that owner, without multiplying it across the q/tag fibre.
2. Connect the remaining four real rejection types and the correct original selected-count weights, then establish an **upper bound in the required direction** on the signed arithmetic-history residual. The current source only exhibits the exact gap.
3. Complete the original request-level Buchstab/retention suppliers, all-action CLOSED-CELL count induction, correct base/switched/seed/floor, feedback integral and original PP/same-rho consumer.
4. Complete native-history Theta/count control and a single genuinely shared nested causal 430+11 construction.
5. Install the exact pinned source-only import closure, incrementally compile this source and direct imports, kernel replay, transitive-axiom audit, and evaluate any finite certificates rather than assuming their success.

**完整 h34 稿内证明仍未闭合。**
