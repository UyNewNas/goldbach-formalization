# P3.5: explicit lossy J price for the actual opposite block

## Baseline and files

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`2f0f09d632e4a53fe5ebe95c57119f46c5629015`. The containing commit is
the new SHA. Packet directory:
`docs/source-only/20261120-p35-opposite-block-transport/`.
`Part3OriginalOppositeBlockTransport.lean` SHA-256:
`5334b41dcd8f54510e31c8bba78eb39a67aa93450246c6311f0e8140e5df372b`.

## Candidate result and exact losses

The parent opposite-block inequality retained four unknown full-J values,
two for each original physical chart. The present candidate replaces
those four expressions with explicit, already-written transport prices,
at both actual physical weights, while leaving the actual cuspidal
complement and continuous terms visible. Let V=2^j, m=classicalMScale j
=V-1/2, Z=fixedZ of the particular chart and W=threshold V Z. Define

    P(C,epsilon,Q,m,W) = max(1,W/(Q+m))^(3/4)
                           * C*((1+Q)*(1+m))^epsilon*(Q+m)*m.

The source's `transportedChartJ` uses the two terms P at Q=Z/2 and Q=Z,
with the original `(2+log(4V+1))^2/4` multiplier. Its
`transportedChartCost` multiplies by the original `(M^2*Z)`, the
chart test budget squared, and the original level-dependent `rawChartN`.
The latter retains the potentially large factor `1+|a|*nu*rowLength/Z`.

`all_raw_chart_costs_with_transport` first chooses C for a fixed positive
epsilon, then bounds every actual chart's raw cost for all marks and
phases. It uses the prior full-J-with-transport candidate twice and
proves nonnegativity of the original marked n-row sum. The exact actual
W is not silently replaced by an initial-range value.
`opposite_block_with_transported_exceptional` substitutes the two chart
prices into the actual opposite-sign `fullBlockMode` inequality, with
its earlier factors 2 and 3 and its exact coefficient. The constant C is
chosen before D, k, chart, mark and phase. The two actual test budgets
are selected before r and the Poisson sign; the phases selected in the
parent proof disappear from the conclusion only because the transport
estimate is uniform in those phases. The proof does not identify the
n-side sequence across levels.

This is an unconditional *candidate relative to its written predecessor
chain*, with no additional J premise. It is not a sharp full-range J
bound: the stated `3/4` power can grow with physical parameters, and
the large raw n cost remains. It does not imply original (24) or the
full-cost 7/32 estimate. The existing B values still need a uniform
test/Fourier budget; R and C are not estimated. No oldform removal,
gap supplier, regular/holomorphic bound or continuous spectral estimate
is manufactured by this substitution.

## Read sources and input boundary

Parent `Part3OriginalOppositeBlockExceptionalBound.lean`, blob
`779f7d38325d249390e8c812c1918a93db063c1d`, and its report were read in
full. `Part3OriginalAllChartLossyPair.lean`, blob
`01f0a4bbdf3deddb96a4533b007cb4beadc8cab6`, gives the exact definition
of `transportedPrice` and `full_J_with_transport`, including its
initial-region parent and explicit 3/4 loss. Earlier positive-only raw
transport blob `e27f337d2bcd25254295bd0964ec834960789a5d` was read: it
does not establish this actual opposite-block statement. The
`AVGJ_APPLICABILITY.md` blob `e4a4e3e8b5798d9f4616a297b9e1082d4130e36c`
was reread, including the distinction between initial and full weight,
and raw versus post-removal n coefficients.

The paper source pin was rechecked: manuscript body at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
is blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching the chain;
the actual (24) passage is in distribution blob
`19f9672bc9b6d455045213c5e23e10433a9569d2`. No new external theorem is
introduced. Pascadi v3, ABL v1, all-K regular input and the numerical gap
retain their prior exact registrations and missing-supplier statuses.
Neither a fixed-level result nor initial AvgJ is represented as the
sharp physical full-weight average.

## Verification and remaining obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axiom check: not performed. Independent review: not performed.
`UNEVALUATED`: yes, including all inherited bodies. The exact import
closure is not staged. `command -v lean` and `command -v lake` each
returned exit 1 without output. No compiler was invoked, so no compiler
exit code or log exists. Configuration pins reread: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot be
checked. Stack 8192 KiB, virtual memory unlimited, unchanged.
`sha256sum` exited 0 with the source hash above. The scan `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` exited 1 without
matches; it is not compilation or a transitive axiom audit. No CI ran.
Root/docs AGENTS lookups were previously recorded absent.

Next stage and replay the precise import chain. Replace or pay the 3/4
transport loss, the raw n loss, and the chart test budget using inputs
actually proved at the required ranges; establish discrete oldform
removal and the gap separately. Bound regular and continuous parts,
connect the same-sign and holomorphic branch, preserve both zero lanes,
actual cutoff tail, 14eta/28eta weights, 128C extension, N-threshold
order and reserve payment. The two exceptional chart prices alone do not
complete any of these obligations.
