# P5.6 → h34 — actual low-presieve original q/tag zero-source branch

Date: 2026-11-09 UTC.
Repository: `UyNewNas/goldbach-formalization`.
Isolated branch: `chatgpt/p5-h34-small-presieve-true-zero-source-20261109`.
Verified predecessor: `cc5593480cf87da6172ad97ebebb64c01189f453`.
Math source commit: `0f31c00ba75ef5f1785bbb7c3b7108e7f1f9c0bb`.
Read-back math blob: `6564ad80fd3a68c494d4aedd404153fd2d26d2b6`.

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, as defined by existing formal proof mapping. Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Why this is a distinct manuscript-internal increment

Previous work established a true original U3/U4 `TaggedReceiver` source, real historical root and second-prime selection, original q/tag fibres with rank-two collisions, and a complete signed source equality with six unpaid lanes. It did not handle the real presieve regime in which the original U3/U4 root cannot even enter the strict historical carrier.

Under the literal assumptions `z0 ≤ (cap : ℝ)` and `z0 ≤ (N : ℝ)^a`, existing `actual_original_stage_requires_large_presieve` would require `(N : ℝ)^a < z0` for any admitted original tagged root. This contradiction is proved on the real original tagged source, not on a made-up history or an assumed full selected owner. No claim is made that the fixed manuscript's actual z0 lies in this low regime.

## New Lean source (146 lines, 7 candidate theorems)

File: `Part5OriginalH430SmallPresieveZeroSource.lean`.

1. `small_presieve_original_stage_empty`: no original U3/U4 tagged receiver survives the actual root-stage policy.
2. `small_presieve_retained_receipts_empty`: the true second-rank q/tag receipt source is empty.
3. `small_presieve_observed_keys_empty`: no chosen true tagged (p,ell) receipt key.
4. `small_presieve_observed_slots_empty`: no observed genuine physical (Q,p,ell) slot.
5. `small_presieve_observed_Qs_empty`: no physical-Q value in the original tagged source support.
6. `small_presieve_complete_original_source_is_unpaid`: for **every signed original q/tag weight** and **every Q-dependent postfilter**, the existing exact complete source ledger specializes to
   `originalSixUnpaidReceiptLanes N cap precision tau z0 lower w = ∑ z ∈ originalTagged N, w z`.
   The kept historical mass, kept arithmetic/history gap and erased historical-position weight vanish because the *original-receipt Q index* is empty. This does **not** say the entire unrestricted first-exit historical list is empty.
7. `small_presieve_original_count_at_root_cutoff`: retains the full original U3+U4 cardinal count at the literal root-cutoff obstruction and zero retained q/tag receipts. U3/U4 overlapping tags are counted separately.

No `q=ell`, synthetic receipt-to-history injection, inferred sign, new c/K, root normalization, row normalization, changed physical Q, external theorem or final H430 bound is introduced. No proof of ordinary PNT/Mertens/BV is attempted.

## Current boundary and next nonduplicative work

These are **candidate proof bodies**, not compiled results. If the true frozen presieve is larger, this branch is merely an exact negative-case lemma. The actual upper H430 selected/full/inherited owner still must be identified on genuine original q/tag receipts and corresponding real Fin-position histories, with stage/z0/root weights and the correct Q. For admitted source, the actual history occupancy, signed first-excluded Euler payment, q/tag collisions and capacity, all six rejection lanes and a sufficiently small *upper bound* for unpaid count remain necessary.

Other unclosed internal work: request-level all-action CLOSED-CELL induction, correct base/switched/seed/floor, feedback-to-integral, PP/same-rho, native-history and one common nested 430+11 causal refinement. No manuscript-local gap is moved into external input assumptions.

**Next precise action:** stage the pinned source-only dependency closure and compile the current modules, then identify the manuscript's actual z0 and split on the physical `z0 ≤ N^a` gate. If the relevant actual case is `z0 > N^a`, prove the genuine selected/inherited owner and quantitative original q-to-history payment; do not count the empty branch as a paid upper-bound source.

## Validation / ownership

Authenticated GitHub push succeeded only on the new isolated h34 branch. Read-back confirmed the math blob and seven declaration names; no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` escape token is present in the new source. `lean`, `lake`, `elan` are absent on PATH; native Git clone/ls-remote failed DNS (`Could not resolve host: github.com`). The source-only import closure is not staged under `ImbalancedChen/`. No Lean parser/elaboration, Lake build, kernel replay, transitive axiom audit, GitHub CI compile or numerical430 replay was executed. **No COMPILED / green credit.** No P1.4/P3.6, production, CI/toolchain, manuscript, main branch changes, force push or merge.

**完整h34稿内证明仍未闭合。**
