# P3.5: actual per-mode test seminorm

This component implements the fixed-order Fourier payment in Appendix A.5 of
the frozen 1106 text. The fixed compact box separates the actual amplitude into
Fourier modes; its coefficient decay must pay for the Bessel test derivative
cost of each mode. [Frozen A.5, lines 705–717](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex#L705)

## Actual quantities and quantifiers

The tests and coefficients are the existing period-64 `spectralTest` and
`actualCoeff`, indexed by `ell : Fin 4 → ℤ`. For `Y > 0` define

\[
S_d(\ell,Y)=\sum_{n=0}^d\sup_{q\in\mathbb R}
 Y^n\left|\frac{d^n}{dq^n}\operatorname{spectralTest}(\ell,Y)(q)\right|.
\]

Each supremum is a real `sSup` of a nonempty, bounded-above range. The source
proves these conditions explicitly, as well as nonnegativity, domination of
each evaluation and a polynomial upper bound. This avoids relying on the
totalized value of an unbounded or empty real supremum.

For every fixed natural order `d`, the result chooses a positive constant
before `rho`, `sigma`, and `Y`. For `rho ≥ 0`, `|sigma| ≤ 1`, `Y > 0`, it proves
both summability and

\[
\sum_{\ell\in\mathbb Z^4}
 |\operatorname{actualCoeff}(\rho,\sigma,\ell)| S_d(\ell,Y)
 \le C_d(1+\rho)^{4(d+3)}.
\]

The supremum is taken separately for each mode and each derivative order,
before the finite derivative sum and infinite Fourier sum. The hypotheses do
not assume the desired derivative bound, weighted summability or transform
estimate. The actual weighted Fourier theorem supplies the majorant.

## Reuse and the new derivation

The supplier retains selected phase and all-order test-jet declarations from
historical M/R20 sources under their existing names and namespaces. The
finite-order constant and its positivity proof come from S22. Exact donor
commits, blobs, ranges and hashes are in [DONOR_EXCERPTS.json](DONOR_EXCERPTS.json).
The frozen extraction and [repair patch](SOURCE_REPAIRS.patch) separate old
proof reuse from compiler-driven expression repairs. Acceptance of this
selection does not promote the full historical M/R20/S22 modules.

S22 already controls a sum evaluated at one common test point. The new step
is the sum of the individual per-mode suprema. The existing all-order pointwise
bound makes each range bounded. For `n ≤ d`, monotonicity of
`(1 + |ell 0|)^n` pays for all derivative orders using one degree-`d` Fourier
weight. Nonnegative domination gives actual summability before the infinite
sum is compared with the accepted weighted budget.

The 55 project dependencies in [DEPENDENCY_CLOSURE.json](DEPENDENCY_CLOSURE.json)
remain byte-identical to the starting head and donor snapshot. Their imported
environment and historical receipts are reused; they are not new owned
strict-compilation or kernel-replay targets.

## What remains outside this component

The frozen text cites Pascadi Lemma D for the test-function estimates. This
component supplies derivative costs for that application, but does not prove
the external lemma or yet identify the actual positive- and negative-sign
transforms with every normalization in that input. It retains arbitrary fixed
`d`; it does not assert that `d = 4` is a sufficient order for Lemma D.
[Frozen Appendix B, lines 1025–1028](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex#L1025)

The already accepted whole-height consumer still needs the actual cumulative
energies and low/high transform envelopes, uniformly over the physical
families. The actual Y04 row adapter still has six registered source
dependencies whose bytes have not been recovered in the checked scope.
Those old proofs are not replaced with new implementations. ABL, Kim–Sarnak
and Pascadi remain external inputs. This component alone does not establish
the full spectral polynomial (96), the returned estimate (97), or P3.5.
[Whole-height receipt](../../continuation-20261125/continuous-height/RECEIPT.json)
· [Remaining mathematical interfaces](remaining-math.md)
· [Incremental source inventory](new-source-inventory.md)

The new supremum payment is a fillable omitted manuscript derivation. The
observed supplier compile failures concern name resolution and Lean API
compatibility. The actual-transform matching is an interface obligation;
the Y04 recovery issue is a source-availability condition. These checks do
not provide evidence of a substantive mathematical gap in the frozen text.
