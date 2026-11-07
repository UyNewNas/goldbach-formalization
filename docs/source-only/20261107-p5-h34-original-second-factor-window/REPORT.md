# P5.6 → h34 — actual original selected quotient, second historical candidate window

Date: 2026-11-07.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified predecessor HEAD: `d0ed19ad870859e6ede51ff11d40dde08e06d548`.
New mathematical source commit: `202747694fe2611d87af804f38b8dccd3fd41d8e`.
Lean source Git blob: `2f44aaa42d915a98fcfe7a5e927e098cd9f4518d`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual addition

New module `Part5OriginalH430OriginalSecondFactorWindow.lean` (246 Lean lines, 8 candidate theorem bodies, 2 definitions).

The preceding packet proved that one actual rank-one history root candidate carries mass `1/(p-1)`, not one mark for each original quotient q. Existing post-root candidate facts treated primarily *rejected* raw quotient obstructions. This packet instead begins with the actual **original selected** U3/U4 `originalTagged N` source and its genuine `ChenPrimeRough (N^a) q` quotient sieve.

It establishes candidate proof bodies for:

1. `original_quotient_is_rough`: every actual original selected (tag,p,q) satisfies the original q-roughness test at the unchanged `N^a` cutoff.
2. `original_quotient_factor_lower`: every prime divisor ell of that q satisfies `N^a ≤ ell`; this is a derived arithmetic-source fact, not an extra premise or new input.
3. `original_factor_in_rank_one_suffix_iff`: at a literal enumerated first-stage candidate with prefix [p], for a prime divisor ell of this q, `ell ∈ c.remaining ↔ ell < p`. This reads the actual strict suffix; the root's real cap and q coprimality with N enter its proof.
4. `original_factor_next_candidate_iff`: equivalently, the original next-selection enumerator offers ell exactly when ell < p.
5. `possible_original_second_iff`: at the true per-(tag,p) physical Q and Boolean root retention, a two-stage **candidate** exists iff the original root is admitted and ell < p, for an actual prime factor ell of the original q.
6. `second_candidate_true_mass_sign`: the genuine second next-selection candidate has positive parity and mass `(1/(p-1))*(1/(ell-1))`, not q-receipt unit mass.
7. `possible_second_factor_window`: any such genuine candidate factor lies in the half-open manuscript-derived interval `[N^a,p)`.
8. `stage_second_candidate_eligibility_signed_ledger`: exact signed partition of the full admitted original tagged q occurrences into those with and without a prime factor below their selected p, retaining arbitrary q/tag-dependent signed weights.

This advances a real missing **candidate eligibility** prerequisite for tracking original q beyond the first rank. It does NOT claim that q itself is prime, that a second-rank candidate passes the Rosser test, that each candidate is a unique final history owner, that repeated q/tag fibres can be charged multiple times, or that a signed count-to-history payment bound holds. The no-factor branch and any further policy-rejected branch remain UNPAID.

## Restrictions and outstanding manuscript-internal obligations

No changes to P1.4 or P3.6, production Lean modules, external analytic theorems, tools, CI or fixed manuscript. No `sorry`, `admit`, custom axioms, unsafe/native proof escape or target-equivalent licence.

Still open: choose the actual manuscript z0 and lower/upper stage; derive the second-rank original retention predicate and match it to the real full/selected/inherited filter; build the genuine q-sensitive owner map with occurrence and sign/mass multiplicities; pay roots blocked by cutoff/strategy and all remaining rejection lanes; orient negative Euler exit corrections correctly; close the CLOSED-CELL all-action induction, base/switched/seed/floor, feedback-to-integral-to-Theta-to-count and local PP/same-rho; native-history mass and common nested 430+11 refinement.

The original c/K, root norm 7/2, row norm 12, true alpha and same-Q rules remain untouched.

## Validation and next action

The remote source blob was read back and compared against the verified predecessor; the mathematical-source commit changed only this newly added independent file. A text-only forbidden-token scan found no proof escapes. No Lean elaboration, compilation, kernel replay, transitive axiom audit, heavy CI, independent review, or numerical430 finite evaluation was run; inherited finite checks remain UNEVALUATED. The results are candidates without formal credit.

Next: inspect actual retained rank-two transitions for these q-prime-factor candidates, then bind them to the original full/selected/inherited owner/filter and signed weights. Prove the complement's actual mass/payment separately. Never convert one root or second-stage candidate into multiple paid q occurrences by reindexing.

**完整 h34 稿内证明仍未闭合。**
