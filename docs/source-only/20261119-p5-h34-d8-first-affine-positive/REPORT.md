# P5.6 → h34 | original D8 moving first-affine positive integral

Date: 2026-11-19. Baseline: `ba479ca0075afd6900f09c7e8efc49dce95def9c`.
Repository: UyNewNas/goldbach-formalization, branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d`.
Scope: SOURCE_ONLY / PARTIAL_SOURCE_INCREMENT / UNCOMPILED /
UNEVALUATED / FULL_H34_OPEN.

## New manuscript-internal source

New module `Part5OriginalH430D8FirstAffinePositive.lean`
(190 lines) establishes a fresh rational
lower certificate for the first MOVING affine D8 subinterval,
`[uLo,cut]=[50/227,1265/5648]`, using the actual lower
support line `1-(16/5)u` and the original upper vHi=10/29.

The original logarithm parameter at the LEFT endpoint is exactly
`249700/191821`. The candidate Lean proof establishes that the
first-affine parameter increases throughout that unchanged interval,
and that `u(1-u)` stays below `cut*(1-cut)`. Its two-term
RationalLogCertificate.check_sound and integral_mono_on give

```
(1/200 : ℝ) ≤ ∫ u in Ioc uLo cut, firstSlice u
```

Independent Python Fraction arithmetic found the exact underlying
lower mass to be
`13544627527299486626688/2407295664371530262441617`
(approximately 0.005626491057), strictly above 1/200.
Python arithmetic is NOT a Lean theorem verification.

A second local candidate theorem includes this first-piece contribution
in the real d8Logs while retaining the second piece as nonnegative.

## Important non-double-counting constraint

The previous exported `genuine_d8_four_cell_ge_103_per_1000`
already concludes `103/1000 ≤ d8Logs`, with the first moving
piece included as a nonnegative term. Hence `1/200` CANNOT simply be
added to `103/1000`. This packet makes no stronger seven-source
lambda claim. Improving the global lambda requires exposing an
independent second-only integral certificate and then exact gluing.

## Exact verification boundary

Read previous packet and source; checked current branch HEAD was exactly
`ba479ca0075afd6900f09c7e8efc49dce95def9c` before write. Local `lean`, `lake`, `elan`
were not available; git HTTPS DNS lookup failed. Source-only text and
exact Fraction arithmetic are the extent of local checks. No Lean/Lake
compilation, kernel replay, axiom audit, finite certificate or new CI
run is asserted. No CI, dependencies, P1.4, P3.6, c/K, original
root 7/2 / row 12 normalization, alpha or same-Q is modified.

## Still open

- Refactor/prove a standalone original D8 second-only 103/1000 theorem,
  combine with first-only 1/200 and prove the full seven-source ≥0.65.
- Compile this and inherited modules using the pinned v4.33.0-rc1 Lake
  closure, fix actual errors; kernel replay and audit transitive axioms.
- Complete fixed count intercept, frozen F seed, request-level
  Buchstab/retention/bank all-action induction, real U3/U4 selected
  source, owner weights and rejection, native-history, PP/same-rho,
  integrals–Theta–counts and one nested 430+11 causal refinement.

Complete manuscript-internal h34 remains OPEN.
