# P1.4 — original sign-matched physical high-q witness

## Verified continuity
Predecessor: `7e995350bbdc42d9949f536cee4b2a57d3387df5` on `chatgpt/p1-full87-nonzero-beta-physical-cut-20261107`. Its REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF, full candidate, signed helper and actual Chen source were read. Current task branch: `chatgpt/p1-full87-signmatched-residual-witness-20261107`; source commit `63abdde17b07e8366c91201666352986e726ee37`.

Original candidate: `docs/source-only/20261107-full87-signmatched-residual-witness/P4AOriginalFull87SignMatchedResidualWitness.lean`; Git blob `9b5d53b6087a8d223d98fb79d4b6201047bc9b84`; 157 lines.

Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; body Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native 09b97db5764ade1246bfb77206baa1b124760958; c=49044063/25000000, K=8452171/1250000; unchanged.

## Actual correction of a gap in the prior witness

The prior theorem `activeMaxTest_false_has_nonzero_beta_factor_and_leaf` only returned a factor on which PLUS **or** MINUS beta was nonzero and an unrelated maximum-product retained terminal. The beta sign need not match that terminal's parity, so this cannot be used to charge a signed term. This is not a cosmetic concern: for a positive terminal with beta+ = 0, beta- != 0, and q > X, the old OR gate may fail although the literal physical terminal contributes exactly zero.

This packet proves a NECESSARY, not sufficient, witness for a *nonzero literal* source. For the original full modulus q = a*prod(leaf.selected) and test F:

1. If the original `attachedLeafTest` high-q value is nonzero, there is a displayed small factor a with beta(leaf.positive,a) != 0, q > X **strictly**, and F(q) != 0.
2. If the original `signedTest` is nonzero, an actual retained leaf occurrence with leaf.value != 0 and a sign-matched factor as above exists. The proof uses the original `signedTest_eq_leaves` and does not deduplicate the leaf list.
3. If the original `ordinarySaving(old-minus-new, highQTest X F)` is nonzero, such a leaf belongs to ONE OF EXACTLY the two unchanged policies: own-sixth `actualParent` or finite eighth `finiteCap`, at the same prefix, sign, mass and remaining carrier. No new policy is introduced and no relative sign or cancellation is inferred.

In symbols:
$$
\mathrm{OrdinarySaving}_{>X}(s;F)\ne0
\Longrightarrow\exists R\in\{R_{old}(s),R_{new}(s)\},
\exists\ell\in\mathrm{RetainedLeaves}_R(s),
\exists a\in A_{small}:
\ell.value\ne0,\ \beta_{\ell.positive}(a)\ne0,\ 
X<a\prod\ell.selected,\ F(a\prod\ell.selected)\ne0.
$$

**This does not reverse the implication:** an identified sign-matched leaf need not survive sums across factors, leaves, or old-minus-new. In particular this does not turn failed OR gates into positive lower bounds, physical PP admissibility or any H_N payment.

## Checks and sharp limitations

- GitHub source commit `63abdde17b07e8366c91201666352986e726ee37` and readback blob `9b5d53b6087a8d223d98fb79d4b6201047bc9b84` confirmed.
- Source lexical scan: no forbidden proof escapes. Raw brackets 7/7 and parentheses 82/82. No Lean compilation or elaboration occurred.
- 4,000 deterministic **synthetic** signed first-exit instances checked the necessary witness implication. 1,538 had nonzero synthetic sum; 0 lacked a true sign-matched and nonvanishing test witness. In 218 cases the prior OR criterion signalled failure but no actual sign-matched high-q leaf-test witness existed. These are model tests only, not original Rosser values or saved87 replay.
- Fixed manuscript PP statement `eq:current-PP` inspected: the external conclusion keeps the SAME full-q rho and smooth W; a generic X=N^(7/32) is not licensed. 7/32 is spectral; 599/1000 is a pre-adjustment support cover.
- No source archive certification, Lean/Lake, kernel replay, transitive axiom audit, independent review, CI dispatch, Codex, toolchain change or reserve payment.

Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT**.

## Unfinished (do not turn parent P1.4 blue)

Authentic frozen saved87 owned eighth occurrences and their parent/owner/trim/beta/source hashes remain missing; the physical integer X and W_N Gevrey and PP class admissibility are not certified. From actual data, classify and charge only sign-matched surviving terms, not a failed OR decision; bound the true high-q signed amount against H_N with ALL full-q, centre/modulus, primitive/endpoint budgets. Ordinary residual integral, rank9 risk, sixth filtering, changed/tagged, saved numerical signed gain and the TWO separate upper reserves remain open.

Exact next action: locate the complete certified saved87 physical occurrence source; audit the manifest hashes, identify original N and the same dynamic parent/leaf tuple. If absent, do not invent counts. Then apply the two actual policies and the present necessary witness to each original occurrence and keep remaining signed charges. Nothing about external PP has been implemented.
