# P5.6 → h34 — actual upper U3/U4 H430 clamp: integral and signed-quarter increment

Date: 2026-11-08 UTC. **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

- Repository: `UyNewNas/goldbach-formalization`.
- Exclusive task branch: `chatgpt/p5-h34-request-admission-20261105`.
- Previous verified remote HEAD: `82e821517eda0c8d7f4a1ecd6e0e825306ddc70c`.
- Mathematical source commit: `51a1e0f9b325e85cb14b3291286514e6af679f8f`.
- New source: `Part5OriginalH430TrueUpperClampIntegral.lean`, blob `238c3989926078afb082ff50700196f6258b4b98`, 154 lines, 9 candidate theorem bodies, 1 definition.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Pinned Lean v4.33.0-rc1, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; neither updated.

## Mathematically new, manuscript-INTERNAL candidate source

This packet uses the genuine `Part5OriginalU34H430Integrable` upper coefficients through the preceding source-only literal phase packet `Part5OriginalH430TrueUpperU34Phase` (previous source commit `ee2072ab8f37aebaaac3d522d7f2e9be72b95fb2`). It neither reconstructs the ordinary lower h-start nor manufactures a q/tag history owner.

1. On the actual strictly positive-width U3 clamp interval `[833/2500,1/3)`, the *genuine* tail denominator `(1/2-t)*t` is positive and at least `1/18`: the algebraic factorization is `(1/3-t)*(t-1/6) >= 0`. The literal tail branch weight `4/((1/2-t)*t)` is positive and at most 72. No H430 table monotonicity or sign hypothesis is added.
2. Exact **set integral** rewrites preserve the literal U3 first and middle bands `[a,57/224)` and `[57/224,833/2500)`, and the exact U4 full domain `[a,59/250)`. These are not an assertion about the original tagged integer receiver count.
3. On the **actual U3 final H430 clamp band**, the candidate equality is

       ∫_[833/2500,1/3) U3H430Coefficient(t) dt
         = (upperAmplitude(2) - upperRoot(H430Numerators,2))
             * ∫_[833/2500,1/3) 4/((1/2-t)*t) dt.

   The real knot-2 scalar is taken out only on this genuine band, not on earlier phases or U4.
4. The Chen root's **negative quarter** is carried under the integral, yielding the same true clamp mass multiplied by `-(upperAmplitude(2)-upperRoot(H430Numerators,2))/4`. This preserves the sign and multiplicity of the U3 labelled occurrence without asserting that the scalar is positive.
5. The U3 and U4 upper coefficients have the exact same integral on their **common coordinate interval** `[a,59/250)`; they nevertheless remain separately labelled costs. Equality of those integrals is not identity of original q/tag source ownership.

The 9 declarations are source proof *candidates*. The new source-only file depends on an earlier source-only packet; staging/import ordering is not itself an installed, compiled artifact. This is a genuine integral-level continuation of the previous pointwise upper H430 phase identification, not the full U3/U4 upper-count estimate.

## Exact remaining manuscript-INTERNAL obligations

- Trace the genuine original U3/U4 **selected-count tagged q source** and its distinct upper H430 historical owner, actual `z0`, root count weights, and the physical full/selected/inherited stage. The ordinary lower h-start cannot be substituted.
- Bind true q/tag occurrence multiplicities and owner/Fin positions, resolve cross-q/tag collisions, erased slots, rejected/no-candidate/cutoff policies, and the arithmetic-vs-history weight gap.
- Prove actual signed Euler complete suffix and first-excluded payment direction; preserve all unpaid lanes until real inequalities pay them.
- Complete request-level Buchstab/retention and all-action CLOSED-CELL arithmetic induction, genuine base/switched/seed/floor, and full feedback integral–Theta–count correspondence.
- Prove manuscript-local PP/same-rho compatibility, native-history proper/equality/inherit mass, and ONE common 430+11 nested causal refinement.
- Integrate/stage the source-only modules, elaborate and compile, kernel replay, audit transitive axioms, and replay finite numerical430 certificates.

No P1.4/P3.6 file, production module, frozen manuscript, default branch, CI workflow or toolchain was edited. Original c/K, root norm 7/2, row norm 12, true alpha, same Q, scalar/specified-cell read distinction and original counting multiplicities remain unchanged. No new external analytic proof, assumed target-equivalent premise, custom axiom or trusted proof bypass was added.

## Recorded checks and handoff

GitHub remote source commit `51a1e0f9b325e85cb14b3291286514e6af679f8f` was read back; the new blob is `238c3989926078afb082ff50700196f6258b4b98`. Comparison to the prior branch head returned exactly one added 154-line Lean file, zero deletions and no modification to existing files. An independent static scan checked balanced nested Lean comments and delimiters, and found none of the prohibited proof escape tokens. **These are NOT Lean parsing, elaboration, compilation, kernel verification or an axiom audit.**

**NOT RUN:** Lean elaboration/build, kernel replay, transitive axiom audit, numerical430 certification, CI or independent proof review. The finite certificates remain **UNEVALUATED** and formal green credit remains zero.

**NEXT:** Trace the original upper H430 U3/U4 *selected-count* source from the frozen manuscript and original count module into this now concrete upper integral; do not infer a q/tag owner from equal coefficient integrals. If matching already has a successor, move to the next unsolved exact consumer instead of adding another abstract Boolean filter.

**完整 h34 稿内证明仍未闭合。**
