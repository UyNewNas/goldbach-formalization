# Part 1 round 5 — integer rough cutoff checkpoint

P1 parent SHA: `e12eb5dfb84817c29e9968560c40d29be550a935`.
Frozen manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Common mathematical baseline: `1a80c1bcce67886f699d097fc37fd245cd3620bf`.
Pins: lean4 v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, goldbach 09b97db5764ade1246bfb77206baa1b124760958, all unchanged.

## New self-contained mathematical step

The genuine rough-prime carrier tests an integer prime with `p < cap`,
while historical Ico cell ownership implies `p < N^b`. Using a bare
`floor(N^b)` for `cap` can drop the endpoint integer prime when `N^b`
is nonintegral. The new `historicalIntegerCutoff N b = floor(N^b)+1`
covers all strict real-cube primes without exceptions at integer walls.

`ImbalancedChen.HistoricalFifthIntegerCutoff` proves strict prime coverage,
two exact finite normalized identities, and two genuine fifth common-cell
integral limits with both the enumeration cap and moving outer cutoff
specialized to that literal integer. It preserves the real old4/old5
ancestor chain, existing Ico selection, separate own-cube gates, and
new-minus-old signed normalization by directly applying the previously
verified cutoff-invariance and actual policy theorems.

This does not prove the manuscript's full adopted numerical caps.
It does not claim the naked floor is safe, nor the separate total density
limit of either policy, nor the final 1+1.75 inequality.

## Initial verification status

At this checkpoint the new source and a defining-module, complete
compiler-type and transitive-axiom audit source are submitted.
The root imports `HistoricalFifthIntegerCutoffAudit`, so the existing
strict Lean core build, bundled original leanchecker, and root axiom audit
will include the new declarations. **CI status is PENDING** until the
exact pushed SHA runs and returns. Prior P1 verified historical
geometry/integral/fallback leaves are imported without modification.

Next smallest step is to receive the actual CI result. Resolve specific
compiler messages if failing, otherwise archive the exact run/job,
source, olean and direct-import identities, full compiler types, axiom
census, and original leanchecker log. Do not describe this source-only
handoff as a new successful local three-gate receipt.

Remaining non-inferred inputs: adopted J/I/old/nu/cap rows and ancestor
identities; complete later/earlier history integrals and adopted
numerical certificate; remaining signed physical distribution, global
boundary, and final counting bridges. Part 0 integration is separate.
