# P1.4 — exact max-small-factor pruning and original physical failure witness

## Recovered fixed chain
- Previous task HEAD verified LIVE: `3fd40b31f9d823848ab43981bb50cd55db203365`, branch `chatgpt/p1-full87-pruned-terminal-cutoff-20261107`. This is not a reset point.
- Isolated successor branch: `chatgpt/p1-full87-max-small-pruned-witness-20261107`. Source commit: `0a73ae238d2233feb1e5c85c31cd1725a1ca95f7`.
- Full new Lean source: `docs/source-only/20261107-full87-max-small-pruned-witness/P4AOriginalFull87MaxSmallPrunedWitness.lean`, 248 newline-separated lines; Git blob SHA-1 `619365cd3cd6800b817e4ae913e1d776a0d3f225`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native 09b97db5764ade1246bfb77206baa1b124760958; c=49044063/25000000, K=8452171/1250000 unchanged.

## New finite manuscript-internal candidate (NOT kernel-checked)
The predecessor's exact `withinPhysicalCut` had to run for EVERY member of `actualSmallRosserSupport N cap w` and for BOTH original old/new ordinary policies at each real eighth occurrence. The current packet proves the max-factor reduction directly over the UNCHANGED actual finite factor support S:

```
(∀ a ∈ S, a * M ≤ X) ↔ (S.sup id) * M ≤ X
```

Here `M` is the exact ORIGINAL retained terminal ceiling; `S.sup id=0` for empty S. The argument uses natural multiplication monotonicity only, never signed-saving monotonicity. The original sign-selective Rosser beta remains in `ordinarySaving`; no factor or branch is dropped.

- `actualRetainedEnvelope_iff_maxSmallFactor` gives the exact original two-policy physical envelope using the single largest actual small factor.
- `actualRetainedEnvelope_iff_twoMaxTests` uses the predecessor's PROVED-BODY exact pruned predicate separately for actual own-sixth `actualParent` and finite eighth `finiteCap`, on precisely the SAME selectedPrefix, positive sign and remaining carrier. This changes the number of Boolean recursion evaluations from at most 2|S| to exactly 2 per occurrence, plus once-per-parameter max-factor scan. It does NOT establish a saved87 runtime bound.
- `sup_mul_gt_iff_exists`, `maxSmallTest_false_has_original_factor`, and `maxSmallTest_false_has_original_high_leaf` prove that a failed maximum test has a witness consisting of an ACTUAL small-support factor a and an ORIGINAL retained terminal leaf with strict full modulus X < a*leaf.selected.prod. This is not a claim of nonzero beta or net signed rho: it may be a false positive after signed cancellation.
- `ordinarySaving_highQ_zero_of_twoMaxTests` supplies the literal old-minus-new high-q arithmetic zero when BOTH exact tests succeed. No new mathematical licence, arbitrary tree, or target-carrying field was used.

## Checks actually executed
- Read predecessor latest HEAD, REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and all 221 lines of source; prior retained-terminal 347-line source; first-exit tree, original signed helper, manuscript lines 450–520; relevant original full87 reports and archive provenance.
- Root, docs, docs/source-only, predecessor packet AGENTS.md reads returned 404.
- Confirmed original fourth raw dataset (FourthRows17LE.bin, 62,885,159 bytes) and fifth raw NPY files (cells.npy, columns.npy) with manifests exist in `proof-continuation-data`; these are NOT a frozen saved87 owned eighth occurrence table and were NOT used as one.
- Independent deterministic Python synthetic check: 3,500 cases of policy-sensitive retained recursion and actual-factor-style support. All 3,500 all-factor vs max-factor decisions matched; 431 cases had empty small support; 1,284 false maxima had an independently enumerated small-factor-plus-terminal witness. Zero contradictions. SYNTHETIC ONLY.
- GitHub source read-back blob: `619365cd3cd6800b817e4ae913e1d776a0d3f225`; 248 lines; lexical forbidden-escape scan empty and 132 opening vs 132 closing parentheses. Source imports depend on upstream SOURCE_ONLY packets that are not installed as actual `ImbalancedChen/` modules.
- No Lean/Lake execution, no parser/elaborator/kernel check, no actual saved87 archive replay, no independent review, no transitive axiom audit, no CI/Codex, no hardware changes. Both compiler and density reserves remain UNPAID.

## Strict remaining obligations
1. Resolve the actual saved87 archive/source-row provenance and input materialization; the inspected raw fourth/fifth arrays cannot be passed off as 87 owned occurrences. Connect the SAME frozen N, small support, actual dynamic parent and actual finite cap to real row-wise calls and record witness population. Do not invent a PP threshold.
2. Establish the manuscript-licensed physical full-q X and Gevrey/AP conditions; `7/32` is spectral, while `599/1000` is pre-complete-adjustment support inflation, not a proved integer PP X.
3. Turn real source counts and sign-attached costs into a SAME rho `H_N`-normalized primitive/endpoint/centre/modulus/high-q budget, not merely physical high-q existence.
4. Close ordinary residual integral, rank9, sixth-filtered loss, saved87 signed gain and changed/tagged, then separately debit compiler and density reserves.
5. Install/typecheck exact proof dependencies with pinned Lean before any COMPILED/KERNEL_REPLAYED status; review transitive axioms and independent provenance. Keep parent P1.4 YELLOW.
