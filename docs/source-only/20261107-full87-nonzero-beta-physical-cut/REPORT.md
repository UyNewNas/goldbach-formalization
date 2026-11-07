# P1.4 — remove zero-beta false positives from the physical high-q gate

## Verified restoration
- Predecessor HEAD: `5c8915d46b6141411deb503d52c4efc496ff024b`, `chatgpt/p1-full87-max-small-pruned-witness-20261107`; read full prior source, REPORT, REGISTRY, INPUT_BOUNDARY and HANDOFF.
- Task-only branch: `chatgpt/p1-full87-nonzero-beta-physical-cut-20261107`; candidate source commit: `c74dde0ac494110246b7ce8eaee56bcafcee220a`.
- New candidate source: `docs/source-only/20261107-full87-nonzero-beta-physical-cut/P4AOriginalFull87NonzeroBetaPhysicalCut.lean`; Git blob `97901d5edf1827b6b0b9279e2ba5c55e90bfe894`; 331 lines.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`, c=`49044063/25000000`, K=`8452171/1250000`: unchanged.

## Corrected physical support and substantive result

The old factor decision used `actualSmallRosserSupport N cap w`, defined as **all divisors of the small presieve product**. The literal terminal sum does use these divisors, but the original `actualSmallRosserPlus/Minus N cap w L` vanish on many displayed entries. In particular, upstream theorems `actualSmallRosserPlus_active` and `actualSmallRosserMinus_active` imply **nonzero beta => a < L**. Therefore the former maximum can be far larger than necessary, and its failure need not even exhibit a factor with any nonzero beta.

The new `nonzeroRosserSupport` filters the EXACT original divisor set by
`actualSmallRosserPlus a != 0 OR actualSmallRosserMinus a != 0`. This is **only a decision support**: the original `attachedLeafTest` continues summing over the original displayed support, retaining sign-selected coefficients, multiplication by full physical modulus and occurrences.

New candidate proof bodies establish:

1. Every retained active factor obeys the **strict** original level `(a : Real) < L`; hence `maxNonzeroRosserFactor <= Nat.ceil L`, including an empty support.
2. `max_active * M <= X` iff **all active factors** satisfy `a*M <= X`. The original old/new retained terminal ceiling is computed separately for the exact own-sixth actualParent and finite eighth cap at the same eighth history. The gate uses **two** cutoff-recursion executions with the same unchanged policies.
3. At any original retained terminal, an active small factor has modulus <= X, while an inactive factor has both original beta values zero. Thus the full original terminal `attachedLeafTest` is exactly zero for the high-q mask, without modifying the terminal sum. `signedTest_eq_leaves` and the previously proved retained-leaf ceiling propagate this to the **original signed first-exit tree**, with leaf-list multiplicities unchanged.
4. With both original continuations passing, the literal `ordinarySaving(old-minus-new, highQTest)` is zero. A failed active maximum has a factor with nonzero **plus OR minus** beta and a permitted original terminal whose full physical modulus exceeds X. A sign mismatch and net signed cancellation are **NOT** excluded.

This corrects a genuine support over-approximation in the previous gate, rather than presenting a new endpoint estimate or using cap monotonicity on signed saving. No source tree, dynamic parent, Rosser beta, policy, owner, inherited mask, eighth occurrence list, physical PP threshold, manuscript constant or reserve is changed.

## Checks and independent boundary

- GitHub readback of full source returned blob `97901d5edf1827b6b0b9279e2ba5c55e90bfe894`, 331 lines. Lexical scan found no forbidden proof escapes; parentheses 201/201 and brackets 17/17.
- Deterministic Python **synthetic** test: 4,000 generated signed first-exit toy instances, with 2 policies, display factors and arbitrary coefficients constrained to zero beyond the test Rosser L. Among them 2,530 cases passed the nonzero-beta joint gate; 351 passed it while the old display-max gate failed; zero high-q signed contradiction in those passing; 2,481 policy-failure events all had an active factor plus actual terminal witness. These are toy semantics, NOT actual Rosser functions and NOT frozen saved87.
- Inspected frozen manuscript `eq:current-PP` around lines 258–278 and physical-support paragraph 476–481; `7/32` is spectral, `599/1000` a pre-adjustment support cover, neither installed as a valid physical integer cutoff.
- Inspected the pinned manuscript verification manifest and compact data listing. The full source manifest explicitly warns that not every original item is in the compact verification package; available eighth-family independent geometric summaries do not themselves supply the original physical full87 owned eighth occurrence list and its dynamic parent for this replay. No real saved87 high-q count was claimed.
- Applicable AGENTS.md paths previously checked at repository root, docs and docs/source-only: none. New proof packet contains no AGENTS.md.
- No Lean/Lake, elaborator/kernel replay, transitive-axiom check, independent review, actual saved87 replay, CI dispatch, Codex, toolchain upgrade, main edit, merge or reserve charge.

**Verification: SOURCE_ONLY / UNEVALUATED / UNCOMPILED / no kernel credit.** Static checks and synthetic data do not establish a Lean theorem.

## Remaining exact duties

1. **Archive:** identify and authenticate original saved87 OWNED eighth occurrence record (physical `selectedPrefix`, `remaining`, actualParent, finiteCap, original small beta, owner/trim, multiplicities). Neither fourth/fifth NPY/BIN nor independent eighth polyhedral certificates can stand in for that record.
2. **Physical PP:** establish the manuscript-licensed actual integer `X`, true admissible full-q parameters and Gevrey test with common rho. No generic `N^(7/32)` threshold is valid.
3. **Arithmetic cost:** replay active-beta two-policy gate on genuine source, track any failing sign-matched terms with the same beta and physical q, and pay signed primitive/centre/modulus/endpoint/high-q budget versus `H_N`. The new failure witness alone is not a nonzero signed coefficient.
4. Ordinary first-exit residual integral, rank9 histories, sixth filtering and the original saved signed gain, changed/tagged, separate compiler/density reserves and final same-rho proof are still OPEN.
5. Stage the exact source-only dependency closure under pinned Lean and obtain compiler/kernel and independent evidence before upgrading any status. Parent P1.4 stays YELLOW.
