# P1.4 checkpoint — exact target-prime deletion on fixed-rank interval

Parent: `06e0a1e088cb2865acd62b96641afe8e5f8c7de3`. Branch: `chatgpt/p1-full87-target-prime-deletion-20261105`.
Candidate: `ImbalancedChen.P4AOriginalFull87TargetPrimeDeletion`.
Manuscript: `9731290e8f53cffda44129906cde6a965eaa869b` §4, lines 379–407, especially `eq:current-raw-density` and the omitted multiplier `prod_(p_last<=p<y, p|N)(1-g_0(p))`, with `g_0(p)=1/(p-1)` for p>2.

## Actual new internal result
The finite set is **N.primeFactors filtered to [lo,hi)**, not an independent source. Its product of primes is bounded by N, so lo^card<=N. When N<lo^(k+1), the true number of omitted target primes is at most k. A finite Bonferroni induction and the actual g0 factor then give:
`0 <= deletion <= 1`, `1-k/(lo-1) <= deletion`, for lo>=3.
Thus, given the actual paper square-test lower cutoff lo and its power gap, the target-deletion factor has an explicit *uniform finite-rank* budget without a distribution assumption. This is not yet an integral or ordinary exit-series limit.

## Next exact step
Bind `lo` to the **actual** rank-j last-prime cutoff from existing original87 square tests, with its exact compact-domain exponent and rounding. Prove a fixed j,k choice yields N<lo^(k+1) for a uniform sufficiently-large-N threshold. Next transport the multiplicative correction into the same original ordinary signed parity exit-series and integrate on the real 87 selected cells, preserving original source, owner, mass, sign-dependent beta and true dynamic parent. Separate positive exit-series convergence and original input normalizers remain to be paid, not assumed by this source packet.

No change to old/new parity policies, sixth level, original87 owner/trim, archive, coefficient c or K. No external analytic result implemented or assumed. No Codex or CI dispatched.

SOURCE_ONLY / LEAN NOT RUN / KERNEL NOT RUN / AXIOMS NOT RUN / INDEPENDENT REVIEW NOT RUN. Retain P1.4 yellow.
