# P1.4 full87: cutoff-directed original retained-terminal branch-and-bound

## Recovery
- Predecessor branch: `chatgpt/p1-full87-retained-terminal-ceiling-20261107`.
- Predecessor HEAD verified before branching: `f2a28e3bd91c560c37a9a4d6e10086ffc20c5107`.
- This task-only branch: `chatgpt/p1-full87-pruned-terminal-cutoff-20261107`.
- Candidate source commit (GitHub read-back confirmed): `81fd28f7802d2210d9fadd1b45b9f7d7974cc57e`.
- Candidate Lean path: `docs/source-only/20261107-full87-pruned-terminal-cutoff/P4AOriginalFull87PrunedTerminalCutoff.lean`, 221 lines.
- Candidate source blob: `8c3246e88f5da628f5516483277c7972a34a988e`.
- Manuscript pin unchanged: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`; unchanged c=`49044063/25000000`, K=`8452171/1250000`.

## Substantive internal result — SOURCE CANDIDATE, NOT KERNEL ACCEPTED
Previous `retainedTerminalCeiling` computes the exact maximum permitted rough terminal product, but recursively explores every original permitted branch. Merely asking whether the *complete physical modulus* `a * terminal.prod` exceeds a cutoff X does not require generating all terminal products.

New `withinPhysicalCut R a X pre positive remaining` is an exact branch-and-bound decision:
1. Empty carrier: compare `a*pre.prod <= X`, with the original strict opposite `X < q`.
2. If `a * (pre.prod * remaining.prod) <= X`, return TRUE immediately; its proof uses strictly positive *actual remaining rough primes* and the previously proved full-carrier ceiling theorem.
3. If `X < a*pre.prod`, return FALSE immediately because the skip-all terminal exists and is already physically over X.
4. Otherwise inspect the same R, same sign, same history, skip branch, and only the originally licensed take branch. There is no new policy, no odd/even parity change, no beta truncation, no proof-target field.

New Lean candidates:
- `prefix_product_le_terminal_ceiling` (skip-all terminal lower bound).
- `withinPhysicalCut_correct`: exact equivalence with `a*retainedTerminalCeiling <= X` under genuine positive-carrier condition.
- `withinPhysicalCut_false_iff_high_leaf`: FALSE is equivalent to existence of an ORIGINAL retained terminal leaf with physical modulus `a*leaf.selected.prod > X`; this is not a claim of a nonzero *net signed coefficient*.
- `actualRetainedEnvelope_iff_prunedTests`: equivalence of the prior terminal envelope to simultaneous tests on the original *own-sixth actualParent* and the original *finite eighth cap* for every original small Rosser a.
- `ordinarySaving_highQ_zero_of_prunedTests`: exact same-parent old-minus-new high-q arithmetic zero when these tests succeed.

This performs real finite support pruning rather than another forced/mixed partition. It is not asserted polynomial time, and no saved87 census, numerical gain or H_N payment is inferred.

## Actual checks
- Live predecessor HEAD and prior REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF and complete predecessor 347-line source read.
- Original `FirstExitTree.lean`, original `OrdinaryRosserFirstExitPolicy.lean`, original full87 owned source, relevant high-q and signed helper, original manuscript blob inspected. Recursive repository tree lists no AGENTS.md.
- Source Git blob written, branch advanced under expected-HEAD check, then source read back: SHA matched `8c3246e88f5da628f5516483277c7974cc57e`? NO: the actual blob is `8c3246e88f5da628f5516483277c7972a34a988e`; see above. The candidate readback matched the latter.
- Static scan zero forbidden escape constructs; 128 opening and 128 closing parentheses; no Lean parser/typechecker was executed.
- Independent deterministic Python synthetic policy stress-check: 3,400 generated positive-prime histories including zero small factors, variable cutoffs, arbitrary parity/history-sensitive original-Boolean-style policies. Candidate recursion agrees with exhaustive ceiling on all 3,400; zero contradictions. Exhaustive nodes visited 481,755 vs 39,243 pruned decision calls; 3,149/3,400 cases used fewer nodes; upper cutoff hit 10,751 times, forced oversize cutoff hit 785 times. These are SYNTHETIC, not saved87 or frozen Rosser admissions; efficiency is not a validated saved87 performance claim.
- Verification `SOURCE_ONLY / UNEVALUATED / UNCOMPILED`; NOT COMPILED, NOT KERNEL_REPLAYED, no transitive axioms audit, no independent review, no saved87 archive replay, no CI or Codex, no toolchain/resource change. No compiler/density reserve paid.

## Remaining precise proof obligations
1. Kernel-check and correct this source before treating it as trusted; no kernel credit was claimed.
2. Locate and replay the frozen saved87 ACTUAL occurrence input, with original owner, trim, inherited branches, full small-beta and dynamic ancestor, without replacing the original census by synthetic data.
3. For an independently proved original PP cutoff and Gevrey licence, run each actual old/new predicate per original small factor; extract high-q witness leaves for failed tests and certify totals against H_N. No fictional `N^(7/32)` cutoff: 7/32 is spectral; manuscript gives 599/1000 as pre-adjustment support inflation.
4. Close original PP/primitive discrepancy, central-prime correction, sixth-filtered signed gains, rank9/ordinary residual integral, changed/tagged and the TWO separate reserve payments.
