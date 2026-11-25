# P2.9: exact location of the nonradial profile excess

Status: **NORMAL COMPILE, INDEPENDENT KERNEL REPLAY AND FULL-OWNED AUDIT PASSED**.
There are 6 owned declarations. This proves the stated support decomposition;
complete P2.9 endpoint credit remains zero.

The 112-line module `ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport`
uses only the existing `P2FiniteMarkedGamma5PhysicalExtension` import.
It retains the original physical profile, all separately tagged old/fresh/tail
coordinates, and every original gate and margin.

## Mathematical result

Define a proper strip at the original logarithmic point by the existence
of a gate g in the original program such that

$
 g\ne\mathrm{product},\qquad
 -\mathrm{width}<\mathrm{margin}_g\le0.
$

If the original physical weight is nonzero and the complete physical
product is at most N, then failure of the original sharp program implies
membership in that proper strip. The complete-product gate itself is
proved to pass from positivity and the complete-product cap.

Thus every supported point belongs to at least one of:

1. the radial excess M>N;
2. the original accepted sharp geometry;
3. an original nonproduct boundary strip.

The three sets are not claimed disjoint. The pointwise inner weight is
at most the sum of the unit indicators of accepted geometry and the
proper strip. With positive log N the same original gate witness satisfies

$
 |\mathrm{margin}_g/\log N|\le\mathrm{width}/\log N.
$

The equality margin=0 is deliberately retained. An original strict upper
face or strict fresh-pair-order face fails at zero; an original closed
face does not. Using the larger one-sided strip is a legitimate upper
bound in both cases. Empty old and tail blocks and repeated prime values
are retained; the result itself is about real physical coordinates and
does not assume primality.

## Existing proofs reused and precise boundary

The proof calls the original `profile_nonzero_margin`,
`physicalProfile_eq_floor_mul_original`,
`physicalProfile_nonzero_lower`, `log_physicalProduct`,
`physicalProduct_pos` and `physicalProfile_bounds`. It does not prove a
new scalar cutoff, derivative bound or smooth profile.

This classifies support. It does not pay the arithmetic mass of a strip,
supply fresh-prime target coprimality, identify accepted geometry with
the original counted source, smooth a selected-history mask, reindex
marked sums, or establish ordinary J or PP. The new SharpSourceInverse
and TargetExclusion modules address separate finite/arithmetic connections.

The relevant 1106 manuscript is
`chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/argument.tex`, the closing positive outer
approximation paragraph of the positive-product proposition (359–407).
This support decomposition is part of the manuscript-internal omitted
connection from the admitted smooth weight to its sharp mass. No
substantive mathematical gap is asserted by the remaining formal work.

## Verification and failure history

The original independent review checked the entire candidate at Git blob
`c7f92f9483abea93502d6aef26927146474b3a74`. Its first strict compile,
task `f77ea43380aa4c838a36345705606101`, rejected the deprecated
`push_neg` spelling. The only repair was `push Not`, preserving the
statements and proof logic and retaining the existing warning policy.

The exact repaired source is Git blob
`2091608eaeec53f3f8b60224fb7b10048642805e`, SHA256
`3d6f71b982a984e7fdd880b21ab496237ebeb656bed24990dedcfec96dff74bd`.

Task `53087f4912ee40c2aa8c90ce10bf5002` reports normal compilation
PASS in 3.317 seconds: six project modules in its closure, five reused,
only this new target compiled. It then failed creating the audit directory
because the P2 filesystem was full. Its later accepted object digest is
`0285b3ed20b8b8d3b5a540dab4f2c6e60a8120a0c6eead3f081036ae8dbe5883`.

The audit-only private-/tmp fallback,
`a21543b68c0541ec8aacb02eaaf66562`, failed before executing the command
because the runner could not create its host-side job log. No source was
recompiled by that attempt. No other session's files or jobs were removed.
After space recovered naturally, task `3e93197765ba4784b7b21113938fd6c1`
reused the existing object without source recompilation and passed independent
kernel replay plus the complete 6-declaration owned/transitive-axiom audit.
Only Classical.choice, Quot.sound and propext were observed. The complete
accepted evidence is under `verification/accepted/`, with exact source/output
bindings in its manifest and REGISTRY. The archive has 96,692 bytes and SHA256
`8a6ff1e7ba4fb0b2e43e2c2974c813fd3814bd90c780a27888145fb8eeb49e7e`.
It contains audit evidence and sources, not .olean objects.
