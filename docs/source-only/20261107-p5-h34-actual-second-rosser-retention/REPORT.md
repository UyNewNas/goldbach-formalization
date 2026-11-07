# P5.6 → h34 — actual rank-two Rosser retention of original q factors

Date: 2026-11-07.
Repository: UyNewNas/goldbach-formalization.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Last verified predecessor HEAD: `63aaba2b945f88f7176103339028ae14530debc4`.
Final mathematical source commit: `9e1f74e4f4f892fbfd6c434ee3de634fd3965a1d`.
Lean source blob: `cef5d51194cfe5ec7bb03f83032afee0062bb7ab`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Actual manuscript-internal advance

Module: `Part5OriginalH430ActualSecondRosserRetention.lean` (267 lines; 9 candidate theorem proof bodies, 2 definitions).

The predecessor `Part5OriginalH430OriginalSecondFactorWindow` proved eligibility of a prime factor ell of the original rough quotient q to appear in the genuine second selection, but did NOT check the second Rosser policy. The current module now keeps the literal first and second next-selection enumerators and evaluates the genuine **second** ordinary Rosser policy at `[ell, arithmeticPrime z]`, using the same actual per-tag/p `originalPhysicalQ` at both levels.

For an original tagged receiver z=(U3/U4,p,q) and a prime divisor ell of q, candidate theorem `retained_original_second_iff` states exactly:

    retainedOriginalSecond N cap precision tau z0 lower z ell
      ↔ selectedOriginalRootStage N cap precision tau z0 lower z
        ∧ ell < arithmeticPrime z
        ∧ ordinaryRosserPrefixAdmissible lower
            (originalPhysicalQ N precision tau z) [ell, arithmeticPrime z].

The original roughness implies N^a ≤ ell, yielding the genuine necessary second-factor window [N^a,p) *together with* this extra Rosser test. No frozen cutoff replaces N^a and no universal Q is inserted. `retained_second_real_sign_and_mass` reads the same real historical candidate's second positive sign and product mass `1/(p-1) * 1/(ell-1)` (not q unit receipt mass).

`retained_U3_independent_of_quotient` and `retained_U4_independent_of_quotient` preserve the key non-injectivity: for a fixed tag,p,ell the historical choice and its policy are independent of which original quotient q happens to have ell as a divisor. This does **not** imply the same historical candidate may pay all those q occurrences separately. U3 and U4 still have separate Q, even for overlapping p.

The q-sensitive predicate `hasRetainedOriginalSecond` asks whether any genuine prime divisor of that original q survives the two-prime test. The signed partition `stage_original_second_retention_signed_partition` then keeps each original tagged receipt in exactly one of:
1. at least one retained rank-two prime divisor;
2. at least one geometrically possible prime divisor but no retained rank-two divisor;
3. no post-root eligible prime divisor.

Finally `original_count_source_five_unpaid_lanes` composes those three classes with the **two prior actual stage-zero root blockers** (cutoff and root policy) to classify the whole original U3/U4 tagged selected arithmetic source. It retains arbitrary q/tag-dependent signed weight w, all q appearances, and U3/U4 overlap. This is an exact bookkeeping candidate, NOT a bound by a historical first-exit sum, and none of the five classes is declared paid.

## Scope, open obligations and correct next action

Still manuscript-internal and unfinished:
- Match rank-two admitted candidates with the real recursive retained frontier and the complete full/selected/inherited history owner, including physical z0, lower/upper phase and later stages.
- Build a genuine q-sensitive, multiplicity-preserving owner and prove sign, coefficient and root/descendant weight compatibility; do not duplicate shared (p,ell) candidates across different q or overlapping tags.
- Pay cutoff, Rosser rejection, candidate-ineligible, policy-rejected, carrier-outside and other non-event lanes, orienting the signed Euler exit correctly.
- Complete all-action CLOSED-CELL induction, original base/switched/seed/floor, feedback-to-integral-to-Theta-to-count, manuscript-local PP/same-rho, native-history masses and the common nested 430+11 causal refinement.
- Compile the staged modules; check kernel replay and transitive axioms; evaluate inherited finite table guards.

No P1.4/P3.6 edits, production file changes, toolchain, CI or manuscript upgrades, or external analytic proofs. No target-equivalent closure premise. Original c/K, root norm 7/2, row norm 12, alpha, physical same-Q and 430+11 reserves unchanged.

## Verification and continuation

GitHub branch advanced by a leased fast-forward from `63aaba2b945f88f7176103339028ae14530debc4` through the source commits `616bad3` and `9e1f74e4f4f892fbfd6c434ee3de634fd3965a1d`. The first source commit was followed by a one-line namespace import fix, whose final source blob is `cef5d51194cfe5ec7bb03f83032afee0062bb7ab`. No heavy compile or CI dispatch; all proof bodies remain candidate SOURCE ONLY. Static source-token checks and remote blob/diff readback are not Lean elaboration or formal verification. Finite certificates are **UNEVALUATED**; green/formal credit remains zero.

Next: take `retainedOriginalSecond` and this original five-lane arithmetic source into the actual `firstExitDepthFrontier 2` and the full/selected/inherited filters, proving an occurrence-preserving correspondence or recording its exact obstruction. Do not repackage the five-lane identity as another abstract count licence.

**完整 h34 稿内证明仍未闭合。**
