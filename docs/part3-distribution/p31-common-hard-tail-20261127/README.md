# P3.1: actual smooth mass at a common hard frequency cutoff

This increment continues accepted source `6bad5965aad974d6187d36477948c8d6273e6281`
and its receipt descendant `092d7b48f470c2733308853e5ec42bf46463fc3c`.
The source package is prepared for exact-commit verification. The subsequent
evidence-only acceptance commit records the observed formal result.

## Manuscript scope and mathematical result

The frozen 1106 analytic appendix is
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/analytic-appendix.tex`, lines 700–703.
Its SHA256 is `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`.
This passage truncates the nonzero Poisson frequencies at a common cutoff,
uses common signed dyadic intervals, and controls the discarded frequencies
by smooth Fourier decay of a fixed sufficiently large order.

For every natural `r >= 2`, the consumer obtains one `A > 0` before all scales,
source data and coefficients. For positive `B`, `C` and `R`, set

\[
J=\left\lceil\frac{10CR}{B}\right\rceil.
\]

`actual_sixSmoothMass_common_hard_tail` proves

\[
\|\operatorname{sixSmoothMass}-\operatorname{actualTruncatedSix}\|
\leq \frac{6AC^2}{R^{r-1}}
\operatorname{sourceAbsMass}(\operatorname{nonzeroSource}(S),\lambda,\omega),
\]

where `S` is the existing `actualSource`. The six pairs of smooth scales are
`(B,C)`, `(B,2*C)`, `(B,4*C)`, `(2*B,C)`, `(2*B,2*C)`, `(2*B,4*C)`.
Every outer `c` carrier still uses the original `C`. Calling the restored tail
bound at `(B,R)` and `(2*B,2*R)` produces exactly the same natural ceiling `J`.
The coefficient mass is explicit; no assumption that coefficient norms are
at most one is added.

The actual truncation is a finite sum of the accepted zero-`m` kernel and both
signed dyadic blocks. The true complementary-subtype series is identified
with the full convergent series minus this finite window. All primary tails
are first combined into a single weighted sum on `nonzeroSource S`, using the
existing partition and pushforward. There is no `keys.card` loss.
The zero-`y` source retains its full integer-frequency kernel. It is distinct
from the Poisson zero-`m` term, which is retained in the nonzero-`y` finite kernel.

## Source recovery and new declarations

| Module | Source declarations | Origin |
| --- | ---: | --- |
| `Part3PoissonNonzeroDecayCore` | 6 | Original quadratic decay supplier |
| `Part3PhysicalCompletedFrequencyDecay` | 3 | Original frequency decay and summability |
| `Part3PhysicalHardSchwartzTail` | 2 | Original hard Schwartz tail |
| `Part3PhysicalCommonHardFrequencyWindow` | 5 | Original common hard window |
| `Part3ActualCompletedHardTailCore` | 5 | Original kernel and weighted source tail |
| `Part3ActualSmoothMassTruncation` | 18 | Current-window, primary and actual smooth-mass composition |

There are 39 named source declarations: 21 recovered declarations and 18 new
ones. The recovered declarations comprise 15 theorems and 6 definitions;
the new consumer comprises 14 theorems and 4 definitions. Generated Lean
declarations are inventoried separately and are not counted as new proofs.

The five complete donor sources are archived under `upstream/` as text.
`SOURCE_FRAGMENTS.json` pins each original Git blob, byte slice and SHA256,
and records any exact mechanical proof-expression adapters. The new verification
group checks the original slices and permits only the specifically recorded
replacements. `EXISTING_WORK_DELTA.json` records the read-only search for
already completed overlapping work before this implementation.

The complete reachable project closure has 81 modules. All 75 project provider
sources are byte-identical to the previously accepted smooth-mass closure.
The six targets are the only new Lean modules. Import choices reuse the
current owners of the frequency, physical kernel, source and coefficient
definitions instead of duplicating those declarations or importing old graphs.

## Verification contract

The added group is `common-hard-tail` in
`verification/verify_part3_continuation.py`. Existing groups, helpers and the
common acceptance flow are unchanged. Final acceptance requires:

- The exact published source commit and a clean working tree.
- Pinned Lean 4.33.0-rc1, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`,
  and all pinned dependency revisions and clean dependency checkouts.
- Six fresh strict compilations with `-t0 -j1 -DwarningAsError=true`.
- Six individual bundled `leanchecker --verbose` kernel replays.
- A complete defining-module declaration inventory, including generated
  declarations, with the existing standard three-axiom allowlist.
- Complete project source/import/object binding, frozen provider objects,
  unchanged baseline proofs, unchanged sources and objects through the audit,
  and the existing source/object gate regression checks.

Imported historical providers remain normally trusted imports. The receipt
does not claim that all external imports or historical provider modules were
individually replayed in this increment.

## Remaining P3.1 obligations

This increment provides a uniform finite source-mass error bound. A final
original-family `x` error budget still requires the manuscript parameters,
coefficient-mass growth and the family cutoff to be connected explicitly.
The original `FixedBlock`/`OriginalData` identification, the zero-frequency
payment and the later spectral `J/A` input are separate obligations.
External Shiu, ABL, Kim–Sarnak and spectral inputs retain their existing
boundaries. The complete P3.1 node is not declared finished by this result.
