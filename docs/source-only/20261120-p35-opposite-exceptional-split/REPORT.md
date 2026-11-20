# P3.5: opposite row, strict exceptional / complement split

## Baseline and deliverable

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`; parent
`965336b353ffb800c8e1546748a6fd19a4695b75`. The commit containing this
report is the new SHA. Its two files live in
`docs/source-only/20261120-p35-opposite-exceptional-split/`.
The Lean file SHA-256 is
`3c71cdfe6739dfbcbca078fdfb95be72321d3412c408836e166014a744f4e3de`.

## Exact candidate and mathematical reduction

For each actual occupied original chart level, with the original
nonzero-residue and positive N conditions and composite trace sign true,
`opposite_row_exceptional_split` proposes the identity

    actual rowSpectrum = finite strict-exceptional native sum
                       + native complement tsum + actual continuous integral.

The finite term is expressed using the previous packet's exact
`chartSignedSlot` and `chartLevelEquiv`, so it retains the same physical
level, Fourier mark, actual test scale, raw level-dependent n-side
functional, common m-side functional, full basis multiplicity and the
factor `8*kTransform`. The complement is a tsum over the same native
index type, outside the exact finite `exceptional q`; no bound for that
complement is assumed. `outside_exceptional_iff` records the strict
eigenvalue predicate, so the 1/4 endpoint stays in the complement. The
continuous density and its integral remain exactly the original ones.

The row's existing `row_spectrum_majorant` supplies absolute summability.
It yields complex summability; finite-set/tsum complement splitting and
the prior sign-specific slot identity give the result. In particular the
split does not take the desired 7/32 estimate, a regular bound, or the
decomposition itself as an assumption. Only the exact mathematically
necessary sign, positivity and original convergence conditions remain.

This result is an **opposite-sign, single-row candidate**. It is not a
bound or a chart-level inequality and does not itself sum the remainder
or identify the positive-sign row. Existing outer coefficient and
physical chart scalar have not been silently added to this row identity.
It does not establish full trace return, all-K regular/holomorphic
estimates, ABL, a spectral gap, full J, or the total 7/32 expense.

## Source and boundary

The parent `Part3OriginalExceptionalChartIndex.lean`, blob
`a9a767f433c3b48a6cd9e057c3f35512d4ffb2a1`, gives the same chart-level
indexing and opposite-slot formula; it is source-only, uncompiled, and
unevaluated. `Part3OriginalPrescribedChartSpectrum.lean`, blob
`fc79ad8d2de109d661b52ba0e9bb83c3c8315e5a`, gives literal opposite
`rowSpectrum`, continuous term and `row_spectrum_majorant`.
`Part3OriginalExceptionalJNativeCompletion.lean`, blob
`a2f2a42763818451f4058d7354698611ebe04c43`, defines the strict finite
exceptional set. The previous packet records the actual sign-specific
chart and original-level sources and their hashes.

Mathlib `Mathlib/Topology/Algebra/InfiniteSum/Group.lean` and
`Mathlib/Analysis/Normed/Group/InfiniteSum.lean` were read at pinned
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; the proposed proof uses the
additive translation of `Multipliable.prod_mul_tprod_subtype_compl`
and `Summable.of_norm`. The actual applied names and elaboration remain
unverified without Lean. No additional external analytic input is
introduced. The prior Pascadi v3, ABL v1 and spectral-gap registrations
and missing-supplier statuses remain unchanged. The m and n sequences
are not identified and no existing initial AvgJ is enlarged here.

The pinned paper source was freshly checked at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`:
`paper/source/manuscript-body.tex` has blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching the chain.
The prior `AVGJ_APPLICABILITY.md` (blob
`e4a4e3e8b5798d9f4616a297b9e1082d4130e36c`) was reread; its original
phase, native coefficient normalization, oldform cost and limited
initial range are not changed. No paper parameters are substituted.

## Verification and remaining work

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axiom audit: not performed. Independent review: not performed.
`UNEVALUATED`: yes, including all predecessor candidate proof bodies.
`command -v lean` and `command -v lake` found no executables; no exact
import closure is staged and no compiler was invoked. Consequently there
is no compiler exit code or compiler log. The repository config pins
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot
be verified. Stack 8192 KiB, virtual memory unlimited; no limits were
changed. `sha256sum` exited 0 with the hash above. A source-only `rg` for
`sorry|admit|axiom|unsafe|native_decide` returned exit 1 with no matches;
this is not a transitive axiom check or compilation. No CI was run.
AGENTS.md was absent at repository root, docs and docs/source-only when
queried at the parent.

Next elaborate the exact import chain and replay/audit it. Sum the row
identity over actual chart levels and restore the original outer scalar
and Fourier coefficient, then prove the corresponding same-sign split.
Bound the complementary regular/holomorphic and continuous terms,
separately pay oldform removal, transform denominators and raw n energy,
and provide the required J and spectral-gap suppliers. Preserve both
zero-frequency lanes, real cutoff tails, the distinct 14eta/28eta
weights, 128C enlargement, original N threshold order and reserves.
