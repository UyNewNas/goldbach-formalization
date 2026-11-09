# P1.4 — quantified original cap-gap on 47 remaining-family inner boxes

## Exact resumed baseline and invariants
Parent: `514411e61dd7efb927f85913dee0b11996a45fc4`, branch `chatgpt/p1-full87-strict-positive-source-integral-20261109`, whose REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and complete Lean file were read. New task branch `chatgpt/p1-full87-remaining45-certified-gap-20261109` started at this immutable parent and has no edits to the existing proof packets. (The **45** string in this new branch's navigation label is a naming slip; the *mathematically correct count is 47 = 14+16+17*. The path and theorem names record 47 accurately.)

Original manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` re-read on this run. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; `c=49044063/25000000`, `K=8452171/1250000` unchanged.

## Concrete new mathematical claim (candidate, not elaborated)

On the **same** original inner box `sourceInnerBox (.remaining d)` with coordinate radius `10^-8` around the pre-existing source-specific rational centre, for all original remaining-family `d` (14 ascending, one seed, 13 nine, two fifty, seven H5 and ten H7), the actual original full87 dictionary satisfies

```text
newCap (.remaining d) t - comparison (.remaining d) t >= 1/20000.
kernel (.remaining d) t >= (4 / (9 * mu^10)) * (1/20000).
```

The key *nontrivial* step beyond the prior strict-positive integral is to use the **actual original row #15**, with `source_common_row d 15 t`, rather than assume a uniform positive gap. Its family-specific exact row lower certificates were already authored (uncompiled):
- ascending14: all 96 literal rows >= `1/10000` within radius `10^-5`;
- seed/nine/fifty16: all actual literal rows >= `11/50000` within radius `10^-5`;
- H5/H7-17: all actual literal rows >= `1/20000` within radius `10^-6`.

The shared `10^-8` box is inside each certified radius. Their minimum is **`1/20000`**, not an unconstrained positive variable. The new candidate proof reduces row #15 to precisely the original `newCap - comparison` and then invokes the previous same-source scaled-gap-to-kernel comparison. It preserves each family’s actual `Cell` constructors, indices, signs of the defining gap, strict source boundaries and full row lists. Original numerical archive indices are **not** used as physical source indices.

For orientation only: using standard volume of an 8D box, the *analytic* integral endpoint implied by these local inequalities for each of these 47 ideal kernels would be
`(1/(45000*mu^10)) * (2*10^-8)^8 = 2048/290805684100673791946979618305846315706730820238590240478515625`, approximately `7.0425e-60`. **The Lean source in this packet formalizes only the row/cap-gap/pointwise-kernel inequality, not the explicit box-volume or full-source integral endpoint.** This extremely small number is not the archived selected gain or a useful `H_N` payment.

## Committed proof source
- `P4AOriginalFull87RemainingBoxGapLower.lean`: 185 lines after import/namespace correction, Git blob `7de21016d0dec150690ca3bc333a2878d2f3eec0`, source commit `52316945ca94baf8e796afa64a89a4685b20d561`; initial draft source commit `483342f9de77bc4164dda51c4b521c0d8e8f11a8`. This code introduces no axioms, target-equivalent structure fields, or proof escapes.
- The source proof depends on existing *SOURCE_ONLY* original-row certificates and the prior integral-comparison packet; it is not independently proven by importing or type-checking those statements.

## Actual verification and limits
- Source file re-fetched from GitHub with blob `7de21016...` and correct branch HEAD after source correction. The three original family row constants and index-15 identification were cross-checked in the genuine source files. Static prohibited-token scan: zero. All this is **not Lean elaboration**.
- Executed `lean --version`, `lake --version`, `elan --version`: exit **127** each (`command not found`). No compatible `lakefile.toml` or pinned mathlib/native checkout in this execution workspace. Accordingly **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. No kernel replay, transitive axioms audit or independent mathematical review.
- No CI dispatch, no Codex, no pin change, no main/master merge/write, no increase in resources, no user-machine access.

## Unclosed internal proof obligations
1. Audit/build this source with pinned Lean imports and fix real elaboration errors. Separate the proof dependency chain from untrusted source-only imports.
2. Provide a kernel-checked exact 8D box measure and **integral** lower for these 47 domains, then cover the other 40 domain boxes. Validate true saved87 `*.witness.json` simplex/quadrature endpoints against original files; current source-only geometry cannot substitute.
3. Match original `Source` with actual N-dependent prime coordinates, the dynamic sixth `actualParent`, shared fourth/fifth history, full signed Rosser coefficients and occurrence multiplicities. No claim of actual physical occurrences.
4. Adapt precise external PP data without proving it; pay low/high-q, modulus and centre-prime, ordinary, raw/finite/filtered, rank9, changed/tagged, two separate compiler/density reserve accounts relative to the same `H_N`, with parameters fixed before N.

External §4 PP **REGISTERED_NOT_PROVED / NOT_CALLED**. Parent P1.4 stays **YELLOW**, not BLUE/GREEN.
