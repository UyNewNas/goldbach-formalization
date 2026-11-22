# Manuscript source continuations — 22 November 2026

This package continues `codex/yellow-closure-20261110` from
`be3b6ef8f8459bf7ac2ba5a2f5e2cc9ed009cad8`. Its mathematical reference is
the frozen 6 November manuscript in
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en`.

All files are **source only and uncompiled**. Independent review of the
mathematical statements, proof text, selected dependency signatures and
scope found no blocking issue in the sources listed below. This is not
elaboration, kernel replay, an axiom audit or complete dependency-profile
qualification. No new green node or full yellow-node closure is claimed.

## Wu complete-product inner cap: unsifted mass

`ImbalancedChen/P2WuProductInnerUnsiftedLoss.lean` extends the previously
published inner-cap loss estimate from prime outputs to the entire
unsifted labelled prime-tuple mass. It reuses the original cap, the
labelled product fibre bound and the native shrinking-box Theta estimate.

For each fixed rank cap, one common threshold precedes every legal
BoxIndex and pays the rank-summed loss as epsilon times the original
`boxTheta`, with the original `Q=N^(1/2-delta)`. The integer collar
includes product exactly N, repeated prime slots and rank zero.

An exact total-variation decomposition separates the loss already paid
by this cap from the remaining wall's outside leakage and inside
attenuation. Those two remaining terms are not estimated here. No new
PP, density or equivalent target assumption is introduced.

Manuscript correspondence: `argument.tex`,
`prop:current-positive-product`, and the positive smooth outer
approximation in its proof. The native Wu dictionary is an existing
formalization interface; this source does not replace the manuscript's
distinct low-product trim.

## Critical constant modes on an actual cusp tail

`ImbalancedChen/Part3CriticalConstantPairTail.lean` proves that, for
Y>0 and nonzero real t, the actual pair
A*y^(1/2+it)+B*y^(1/2-it) is square integrable on y>Y with density
dy/y^2 exactly when A=B=0. At t=0 these two powers coincide and the
correct condition is A+B=0.

The proof retains the mixed term. A positive dilation
c=exp(pi/(2*t)) gives
D(y)+c*D(c*y)=2*(norm(A)^2+norm(B)^2)/y, where
D(y)=norm(F(y))^2/y^2. This also covers negative t. The existing
inverse-height integrability obstruction completes the argument.

The same file applies the result to the ordinary Eisenstein series'
actual unit-period mean at infinity at every positive level.
`ImbalancedChen/Part3NativeCriticalMeanTail.lean` applies it to the
existing horocycle mean in any pair of normalized native cusp frames,
with the actual incoming channel and continued scattering entry.

Manuscript correspondence: `analytic-appendix.tex`,
`app:classical` and `ana:regular-norm`. These results concern the
spatial constant coefficient. They do not identify the formal
Plancherel measure with an individual Eisenstein vector's spatial norm.

The independent threshold basis sqrt(y), sqrt(y)*log(y) is a different
problem from the coalescing two powers at t=0; its mixed classification
is not supplied in this package. Full spectral expansion, normalized
Kuznetsov/large-sieve inputs and the complete manuscript theorem remain
separate obligations.

## One Fine selection and the sharp half-product count

`ImbalancedChen/P1Full87FineSharpReceiver.lean` uses the existing Fine
selection with `nu=1` and `v=19/96`. The same selected epsilon, aligned
mesh and N threshold carry the original high-atom predicates, compiler
expense, density bound and strict coefficient support below
`N^(599/1000)` into the actual sharp half-product count.

For all sufficiently large even N, uniformly for every `1/2 <= b < 1`
and `kappa0 <= 1/4`, the actual endpoint buffer makes the coprime
correction vanish on this source. The resulting count
retains the original signed distribution error and the boundary costs
`ceil(z)` and `T+1`, where `T=2*N^(1-kappa0)`. The earlier full87 RAW /
LICENSED difference also has zero coprime correction at these parameters.
The final coefficient has `rho(1)=1`, whereas that earlier difference
has `deltaRho(1)=0`; the two arithmetic coefficients remain distinct.

This source composes existing density, source-gate and compiled-modulus
results. It does not supply the full signed PP estimate or the remaining
owner-by-owner full87 correspondence.

## saving16: the actual first-cell corner and its signed remainder

`ImbalancedChen/P2Saving16FirstCornerReciprocalResidual.lean` treats
the original ascending cell 0. For an actual selected pair `(s,d)`, it
retains the complete physical modulus `s*d`. If `p` is the canonical
eight-prime prefix of `d` and `h` is its canonical tail, the existing
small/rough and prefix/tail coprimality give the exact identity

`1/phi(s*d) = product_j(1/(p_j-1)) / (phi(s)*phi(h))`.

The reciprocal prefix weight belongs to the exact coprime mean. The
congruence count keeps its original occurrence multiplicity. The
comparison of the original physical change with the compiler correction
retains the actual multiplier: -2 on the original policy's raw support
outside the raw support of policy6, and -1 otherwise. It retains the signed small-prime beta factor,
the selected upper corner and its full complement. The ordinary
`w=0` contribution is identified once per prefix and is not multiplied
by the number of physical pairs carrying that prefix.

The final theorem uses the existing R17 parameter selection and rewrites
its two finite count bounds with this exact same-Q/same-rho identity.
It spends no additional compiler reserve. The quantitative PP bound is
still required. The corner's strict 96-row geometric membership also
retains its mesh condition `12*tau < width(r)`; the finite arithmetic
identity itself does not require that extra condition.

## A short-medium branch on the original physical Fourier fibre

`ImbalancedChen/P4BOriginalShortMediumTriplePayment.lean` considers
the actual two-group HB fibre at the complete scale `x=U*V`, with its
selected head satisfying `U <= x^(1/16)`. It treats actual modulus words
of length three whose first original prime satisfies
`log_N(p_1) <= 25/128`.

The original integer endpoint inequalities imply a total exponent at
most `173/375`. The exact three-group partition and the original small
Rosser factor then give

`Q1^3 * (Q2*Q3)^4 <= V^2 * x^(-1/100)`.

This removes the extra power-bound premise of the existing refined
shared-prime signed-error supplier for this subfamily. The source gives
arbitrary logarithmic accuracy for the norm of the actual complex
signed error, with one threshold preceding the policy, physical fibre,
retained frequency, word and occupied modulus blocks.

`ImbalancedChen/P4BOriginalShortMediumTripleReceiver.lean` carries
this payment back to the original `P.S=wholeHigh` and `P.rho`. It pays
the restoration cost and the existing squarefree-collision error on
that same fibre. Its conclusion bounds the norm of the original
count-minus-exact-coprime-mean discrepancy minus the explicitly retained
other words by `eta*singularNormalization(N)`.

This is a per-fibre payment. The remaining words, longer medium heads
and weighted recombination of all Fourier/HB fibres still have to be
controlled before removing the full `mediumTotal` term.

## h34: original receipt positions in one cutoff-rejected subfamily

`ImbalancedChen/Part5OriginalH430NoPostRootReceiptPositions.lean`
uses the actual original quotient `q` at its selected root prime `p`.
For cutoff-rejected receipts with no prime divisor below `p`, it proves
that the receipt survives exactly those original history positions
whose entire path from the root appends no new prime. Every actual list
position is retained,
including repeated fixed and retained reads, and its physical level
is the original tag/root-cell level.

For each fixed tag and root prime p, the exact history charge is the
subfamily's cardinality times that root's original position budget.
The existing history budget gives the bound
`431*card(subfamily)`, including the origin and the 430 feedback levels.
The source identifies this part of the actual cutoff-rejected R4
entry with its original U3 and U4 origin counts. The other receipts
remain explicit in the presieve decomposition.

Only the already licensed classical U3 band is charged to
`classicalOwnTheta`. That bound retains the cardinality of the other
original receivers as a subtraction from the available account. It
does not pay the U4 or nonclassical subfamilies, discard the extra
repeated-position debt, or close the full signed h34 account
`-(O+E+R4)/4`.


## Current Fourier family: reuse and actual remaining bindings

The current manuscript fixes a finite original prime family. Its HB
coordinate count is at most 6kStar. Existing all-rank Fourier sources,
physical normalization, original-bank logarithmic restoration and
post-modulus cutoff results are reused, with their actual Family and
coefficient hypotheses. Independent smooth-label grids retain their
additional multiplicity cost.

[FOURIER_REUSE_AUDIT.md](FOURIER_REUSE_AUDIT.md) gives the derivation,
exact existing source identities and the remaining actual marked-source
and same-rho retained-mode bindings. No duplicate Fourier Lean file was
created for this task.

## Ten tasks and independent review

All ten task identities were dispatched with the model and reasoning
effort below. Three subagents at most worked concurrently. T09 reviewed
the five later Lean files; T10 reviewed the first three and the Fourier
audit and mathematical scope. One invalid use of positivity in the
short-medium receiver was replaced by the explicit nonnegative-addend
lemma and the revised bytes were re-reviewed. This remains static
review, with no compilation or kernel acceptance.

| Task | Model | Reasoning effort | Result |
| --- | --- | --- | --- |
| T01 | `gpt-6.2-sol` | `high` | Existing-source and remaining-obligation audit |
| T02 | `gpt-6.2-astra` | `xhigh` | Wu unsifted inner-cap source |
| T03 | `gpt-6.2-astra` | `xhigh` | Critical constant-pair and native mean-tail sources |
| T04 | `gpt-6.2-astra` | `max` | Same Fine selection and sharp half-product receiver |
| T05 | `gpt-6.2-astra` | `max` | Actual saving16 first-corner signed residual |
| T06 | `gpt-6.2-astra` | `max` | Short-medium triple geometry and physical fibre payment |
| T07 | `gpt-6.2-astra` | `max` | Original cutoff-rejected receipt positions |
| T08 | `gpt-6.2-sol` | `xhigh` | Current finite-family Fourier reuse audit; no duplicate Lean source |
| T09 | `gpt-6.2-astra` | `max` | Independent P1/P2/P4/P5 static review and repair re-review |
| T10 | `gpt-6.2-astra` | `max` | Independent Wu/cusp/Fourier mathematical and public-scope review |

## Reused source locations and selection

The new sources import existing modules rather than copying their
implementations. `PUBLIC_SOURCE_MANIFEST.json` lists every direct
source-only dependency with its repository path, immutable ref and
exact blob. Production dependencies use the base commit above; their
existing transitive source dependencies are still required.

The additional topic sources come from these unchanged snapshots:

- P1 real source gate and low physical delta:
  `c13d2e9b11f07d694e9d678d8b2bc1943d36e352`.
- P2 original saving16 comparison and upper corner:
  `9b1b19b44e756777738a8b37ef677429c60eb5e3`.
- P5 original signed finite-capacity account:
  `1e6fdd30c9ec63eeb98da2552b1a52eee85f7e74`.

For the transitive module `ImbalancedChen.P4BOriginalMediumAtomFamily`,
use the existing corrected source at the base commit:
`docs/source-only/20261112-resume/t05/lowhead-next/review-r1/P4BOriginalMediumAtomFamily.lean`,
blob `2a4dbb1d03b172bfac62536b6d28fa8bebcc438e`.
This prior proof-body correction preserves the declaration signature.
It is reused as an explicit source selection, without rewriting it.

These records identify the sources used by the review; they do not
certify a complete installation or import closure. The project's Lean
and Mathlib pins are unchanged. Publication uses `[skip ci]`; no
validation run or status-color change is claimed by this delivery.
