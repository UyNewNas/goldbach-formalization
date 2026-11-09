# P5.6 → h34 — actual signed first-excluded Rosser Euler suffix

Date: 2026-11-09 UTC.
Prior h34 verified HEAD: \`1e191e55ff7b94c9e8f72caa064f77680816fbaa\`.
Original task entry: \`0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0\`.
Independent branch: \`chatgpt/p5-h34-actual-signed-euler-suffix-20261109\`.
Mathematical source commit: \`cc1693969a0b146cf3666fee5bcb1629bd4d7852\`.
Source blob: \`33980c9d2253e645c937932715e9ea331f28ec59\`.
Source file: \`Part5OriginalH430ActualSignedEulerSuffix.lean\` (168 lines; 2 definitions, 7 candidate theorems).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Frozen manuscript link and exact object

Pinned manuscript \`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766\`, \`paper/source/manuscript-body.tex\`, blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`. See Eq. \`eq:current-upper-exit\`, manuscript-body.tex lines 378–401: retained Möbius tree equals complete Euler product plus odd first-exit suffix \`h(e) prod_(p<p_last(e))(1-h(p))\`. The separately described full and selected-complement support squares belong to the PP coefficient proof, not automatically to a count owner. The frozen manuscript stays fixed.

The new file reuses the installed \`FirstExitTree\` and \`OrdinaryRosserFirstExitPolicy\` finite signed polynomial machinery. It specializes the exact signed product-plus-correction identity to the **actual** \`roughPrimeUniverse N cap 0 z0\`, original ordinary-Rosser retention, and prime weights \`1/(p-1)\`.

- \`physicalEulerBase\`: unique finite complete Euler product, independent of physical Q.
- \`physicalFirstExcludedSuffix\`: the literal **signed** \`firstExitCorrection\` at real physical Q; it retains all first-excluded unprocessed-prime factors.
- \`physical_retained_eq_euler_add_first_excluded\`: exact finite tree identity on the real carrier, before any analytic limit.
- \`physical_upper_density_eq_euler_add_first_excluded\` and \`physical_lower_density_eq_euler_add_first_excluded\`: match that signed identity to the existing exact small-Rosser upper/lower densities, under the explicit strict physical level \`1<Q\`.
- \`physical_upper_lower_difference_is_signed_suffix_difference\`: common Euler baseline cancels, but **not** the signed first-excluded corrections.
- \`tagged_original_physical_upper_density\`: specialize at the previously constructed original U3/U4 tagged receiver's \`originalPhysicalQ N precision tau z\` (not quotient q); preserve \`1<Q\`.
- \`original_U4_overlap_two_Q_upper_difference\`: two original arithmetic tags at one \`(p,q)\` use **possibly different** physical Q. Their different density contributions are exactly the difference of their signed corrections; no same-Q or zero-collision hypothesis is assumed.
- \`original_U3_quotient_independent_signed_suffix\`: distinct quotient receipts at fixed U3 root p share one physical root correction; they must not be counted as distinct historical exits.

These are finite algebraic identities and exact existing-instance connections. **No proof has been supplied that the six rejected q/tag lanes equal or are bounded by the first-excluded Euler correction**, no signed inequality, no historical owner/selected-count binding, no h34 numerical budget and no external analytic input have been supplied here. In particular this is NOT a proof that the desired signed first-excluded suffix pays the original H430 gap.

## Validation / source-only boundary

Authenticated repository permission was verified; dedicated branch created at the above prior HEAD (not at the original entry). Mathematical commit read back successfully: one new 168-line file, seven theorem declarations, two definitions, zero deletions, Git blob exactly \`33980c9d2253e645c937932715e9ea331f28ec59\`. Forbidden \`sorry/admit/axiom/unsafe\` proof escape scan of that mathematical source found none. No production modules, old source-only packets, P1.4/P3.6, main, CI or toolchain were changed. This branch does not force-push or merge.

Local toolchain preflight: no \`lean\`, \`lake\`, or \`elan\` executable, and native \`github.com\` DNS lookup fails. The \`Part5OriginalH430PhysicalSelectedRootQFibres\` import is still in source-only and is not staged into \`ImbalancedChen\`; this dependency chain cannot currently be elaborated locally. Existing GitHub workflows do not compile this new source-only path by themselves, so an unrelated green CI run cannot validate this proof. **No Lean/Lake compile, kernel replay, transitive axiom audit, finite numerical430 replay or external review** has been performed. All seven declarations are candidates only; COMPILED=false, formal green credit=0, inherited finite guards UNEVALUATED.

## Remaining manuscript-internal work

1. Identify the true upper H430 \`full/selected/inherited\` historical selected-count owner, stage, physical Q, and root weights; do not confuse PP coefficient selected squares with selected-count ownership.
2. Construct the actual mapping from six distinct original rejected q/tag lanes (including U4 overlap and cross-q collisions) to **unique first-excluded** historical prefixes and prove the signed, directionally correct Euler suffix accounting. This file only identifies the true *finite correction* to be matched.
3. Prove effective unpaid-gap bounds, request Buchstab/retention and all-action CLOSED-CELL, base/switched/seed/floor, feedback integral, true PP/same-rho, native history, and causal 430+11.
4. Stage the exact source-only import closure under pinned Lean \`v4.33.0-rc1\` and Mathlib \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`; compile, kernel replay and audit. Do not infer validity from Git hashes or source-only scans.

Next meaningful proof action: match each original exclusion lane's **actual first prohibited prefix** to the physical Rosser first-exit tree under the same tag-specific Q, including parity, remaining prime carrier and multiplicities. Where such correspondence fails, leave the signed mismatch as an explicit unpaid term rather than dropping it. Then compile the finite signed-suffix consumer with pinned imports.

**完整 h34 稿内证明仍未闭合。**
