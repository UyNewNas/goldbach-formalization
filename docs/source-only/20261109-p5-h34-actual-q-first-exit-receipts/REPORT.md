# P5.6 → h34: original rejected fourth-lane first exits at actual per-receipt physical Q

Date: 2026-11-09 UTC. Source branch: `chatgpt/p5-h34-actual-q-first-exit-receipts-20261109`.

- Verified predecessor h34 HEAD: `d44874cf714b818b5f51aafaf4c85a7e47cc7363`.
- Historical original task entry: `0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0` (not the working baseline).
- Mathematical source commits: `0def7e3927ebee04727fceb4f526b148d4210b3c` (initial) and `f878b68530c90ab5351f5c06e140726034eac9e9` (explicit Euler namespace open).
- Source file: `Part5OriginalH430ActualQFirstExitReceipts.lean`, **202 lines**, two definitions and five candidate theorem declarations.
- Source blob read back from GitHub: `59ecc85f653805c7c215cf994218a4f7decfa6ec`.
- **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Why the increment is new

The predecessor signed Euler direction module proves the **global upper finite** first-excluded correction is nonnegative for every physical `Q>1`. Earlier fourth-lane event and signed remaining-product lemmas, however, used one caller-specified constant Q. This packet specializes the **two genuine original q/tag rejection sources** to their own `originalPhysicalQ N precision tau z`. In particular, the same arithmetic p may have U3 and U4 tags with different historical Q; no equality is manufactured. The original quotient q is not a new prime-slot or a fresh signed event.

The two finite classifiers `frozenFailAtActualQ` and `rejectedFailAtActualQ` retain the original tagged receipt and use the original **different** bad-factor functions: `frozenOnlyBad N` versus `rejectedFrozenBad N n tau`. They test `ownPolicyFail` at that receipt's actual Q, rather than assuming constant-Q eligibility across U3/U4.

For every receipt admitted to each respective classifier and every genuine cutoff `z0 ≤ cap`, the new two central candidate theorems exhibit:

1. the exact singleton **rank-two** `actualRankTwoHistory` at `originalPhysicalQ`;
2. the first forbidden prefix `[actualBadFactor z, arithmeticPrime z]`;
3. the original event positive flag and exact bare event mass;
4. the actual signed exit, with **negative** event mass times the entire remaining Euler product from that same historical event.

This is an actual per-receipt **first-excluded event match** for two of the rejection sublanes; it is not a proof that every receipt yields a DISTINCT event. Cross-q and cross-tag key collisions remain an unpaid multiplicity issue.

`actual_Q_two_fail_sources_disjoint` shows the two source sets are disjoint **as tagged receipts**, while deliberately not asserting disjointness after projection to physical event keys. `actual_Q_two_fail_signed_source_split` retains all original arbitrary signed q/tag weights. The last lemma carries the previously established **global upper** Euler suffix sign to the same physical Q for an eligible frozen-only receipt; it explicitly does **not** identify that global suffix with one individual rank-two event or with a paid arithmetic discrepancy.

## Frozen scope and proof boundary

- Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, including `eq:current-upper-exit`.
- Pinned toolchain: Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- No production source, original h34 packet, P1.4, P3.6, manuscript version, parameters, c/K, root norm 7/2, row norm 12, alpha, same-Q structure, other branch or CI configuration changed.
- **No new external analytic input**; existing finite event/receiver and upper suffix interfaces are reused (see EXTERNAL_INPUTS.md).
- No new `sorry`, `admit`, custom axioms, native proof escape or target-equivalent licence is introduced.

## Validation actually performed

- Confirmed GitHub push permission and predecessor ref `d44874c`.
- GitHub content readback confirms the new 202-line mathematical file and blob `59ecc85`; the compare endpoint confirmed the initial fast-forward `d44874c → 0def7e3` with 201 additions/0 deletions, followed by the one-line source namespace fix `f878b68`. Neither changed any production or concurrent-task file.
- The current runtime has `git` but **no `lean`, `lake` or `elan` on PATH**; no pinned local dependency checkout or prior source-only module installation is mounted. Existing CI workflows do not automatically install/elaborate these source-only packet imports, and CI configuration is intentionally unchanged. Accordingly **no successful Lean compile**, no kernel replay, no transitive axiom audit and no numerical430 finite replay occurred. Static prohibition checks and Git hashes are not evidence of elaboration.
- Nothing in the current packet is marked COMPILED or green; inherited source-only proofs and finite guards remain UNEVALUATED.

## Outstanding internal work / next specific step

1. Convert the per-receipt actual-Q first-exit witnesses into a **per-(physical Q,p,ell) unique event-key ledger**, with genuine U4 double tags, cross-q collisions, sign and full Euler suffix preserved, and all nonmatching receipts explicitly unpaid. Disjoint *receipt* sets do not imply disjoint *event* keys.
2. Match the other actual root-gate, carrier-outside and policy-pass rejection lanes; identify **full/selected/inherited** stage owner, original root count weights and remaining first-excluded residuals, without replacing counts by a root mark.
3. Prove the quantitatively sufficient directional original H430 unpaid-gap bound. The nonnegative global upper finite Euler correction does not pay the rank-two signed arithmetic/history discrepancy.
4. Complete request Buchstab/retention and all-action CLOSED-CELL count induction, correct base/switched/seed/floor, feedback integral and manuscript-internal PP/same-rho compatibility.
5. Prove native-history Theta/count and one genuinely common nested **430+11** causal refinement.
6. Stage the exact immutable source-only import closure at pinned versions; incrementally Lean/Lake compile the new module and its direct dependencies, kernel-replay and audit transitive axioms, then recheck finite guards. Do not claim green from textual checks.

**完整 h34 稿内证明仍未闭合。**
