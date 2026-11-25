# P2.9: actual frozen-cutoff target-divisor exclusion

Status: **SOURCE_ONLY_UNCOMPILED**. This increment has **0 formal credit, 0 kernel credit and 0 endpoint credit**. Only Git blobs were created; no source build, cloud job, commit or ref update was started by its author.

## Exact result

The new module is:

- `ImbalancedChen.P2FiniteMarkedGamma5TargetExclusion`

It reuses the original frozen constants and the existing radial definitions:

\[
 a=\mathtt{frozenLeafCutoffFloor},\qquad
 \beta=\mathtt{cutExponent}=a/2>0,\qquad
 \operatorname{cut}(N)=N^\beta,\qquad
 \operatorname{norm}(N)=\log N/N,
\]
\[
 K=\mathtt{frozenSourceRankBound},\qquad
 \mathcal M=\mathtt{P2FiniteMarkedGamma5RadialTupleCount.multiplicity}
           =\sum_{k=0}^{K} k^k.
\]

For each rank \(k\), `noncoprimeTuples N k` is the original bounded ordered-prime enumerator `Part3.labelledPrimeTuples k (2*N)`, filtered by all three literal conditions:

1. Every coordinate is at least the existing `cut N`.
2. Its complete product is at most \(2N\).
3. The complete product is not coprime to the target \(N\).

Every coordinate and every repeated prime remains in the tuple. The new `noncoprimeCount N` is the sum of these cardinalities over the fixed type `Fin (K+1)`, with **mark multiplier 1**.

The public quantitative theorem is

\[
 \operatorname{norm}(N)\operatorname{noncoprimeCount}(N)
 \le \frac{2\mathcal M}{\log 2}
       \frac{(\log N)^2}{N^\beta}\qquad (N>1).
\]

Consequently `normalized_noncoprimeCount_tendsto` proves that this normalized full-rank count tends to zero. `absolute_noncoprime_payment` gives its absolute epsilon bound. `absolute_noncoprime_rank_payment` uses one eventual threshold for **every** \(k\le K\).

The bound uses only a fixed rank sum; its constants do not depend on the moving target, a tuple, or its prime divisors. The zero-rank case is included: the empty product is \(1\), so its noncoprime carrier is empty. The fibre bound retains the usual \(0^0=1\). No numerical evaluation of the enormous frozen rank is performed.

## Existing arithmetic proof reused

The exact original supplier is:

- `ImbalancedChen/P5U7ActualRoughTargetExclusion.lean`
- Git blob `def029a71dc650b0b409c17427e69ec63c945345`
- SHA256 `d188f8393cd621b73ae08746287ce02164171a3a5b86d7c6de007bf87fedd94f`

Its `p5U7ActualBadRough N x z` is the original `roughNumbers x z` filtered by failure of coprimality with \(N\). The theorem

`ImbalancedChen.p5U7ActualBadRough_card_le_log`

has only the hypotheses \(0<N\), \(0\le x\), \(0<z\), and proves

\[
 \#\{0<m\le x:\ P^-(m)\ge z,\ (m,N)>1\}
 \le \frac{\log N}{\log 2}\frac{x}{z}.
\]

Its existing proof covers each excluded integer by a prime in `N.primeFactors` and a positive quotient. Its logarithmic prime-factor estimate is the existing `chen_primeFactors_card_le_log` in `ChenInitialCorrectionBudget`. Those proofs are called without modification.

The decay theorem is the existing `ImbalancedChen.tendsto_nat_log_pow_div_rpow` from `PowerErrorBudget`, instantiated with logarithm exponent 2 and the already proved `cutExponent_pos`. No prime-number, Buchstab, distribution, sieve-coefficient or ordinary-\(J\) estimate is introduced as a hypothesis.

## The new finite connection

`product_mem_bad` sends a tuple to its complete positive integer product. The existing prime-divisor floor theorem proves that this integer is `cut N`-rough.

`rank_bound` then sums over those integer fibres and calls the original

`ImbalancedChen.p5z_marked_prime_product_fibre_card_le`.

The product map is not injective. Each fibre is charged by \(k^k\), including reordered and repeated prime coordinates. `all_ranks_bound` uses the already defined symbolic \(\mathcal M\).

This construction follows the existing proof structure in:

- `Part5OriginalH430ClassicalProperWallMarkedOutputs.rank_bound`;
- `Part5OriginalH430ClassicalProperWallSeedCredit.all_proper_ranks`;
- `Part5OriginalH430ClassicalProperWallSeedCredit.target_bad_small`.

Those classical consumers use the cutoff \(1/96\), `Fin 201`, and, for their full marked payment, a multiplier 20. The new consumer uses the actual frozen cutoff and rank with multiplier 1. The adapted proof bodies are **not** claimed to be byte-identical copies of those old consumers.

The bounded tuple carrier is the same `Fin (2*N+1)` representation used by the existing radial consumer. A positive prime coordinate divides the complete positive product and is therefore at most \(2N\). This increment proves its payment on that explicit enumerator; it introduces no new unbounded sum or separate natural-carrier identity.

## Manuscript role and remaining boundary

The frozen 1106 manuscript is `UyNewNas/chen-imbalanced-semiprimes` at `a988cba584d803ae2856a0de50efb582f4f3dd6a`:

- `paper/release-20261106/en/sieve-appendix.tex`, 634–660: the original pair/rough-cofactor source and the same nonnegative marks;
- `paper/release-20261106/en/argument.tex`, 359–374: bounded rank, a fixed positive prime floor, complete product \(O(N)\), and the ordinary-mass premise;
- `paper/release-20261106/en/argument.tex`, 400–407: positive outer approximation, with \(N\) tending to infinity before its approximation error;
- `paper/release-20261106/en/sieve-appendix.tex`, 1090–1101: fixed positive cutoff, finite queries before \(N\), and absolute errors.

The manuscript does not state this exact auxiliary finite-carrier theorem separately. It is an elementary source-deletion payment needed when comparing the ambient prime tuples with the original `primeWindow N`, whose fresh primes must be coprime to \(N\). It is an arithmetic deletion, not an affine geometric wall. It is also different from the reciprocal-totient correction in `argument.tex`, 379–388, which is a correction over sieve moduli.

This module supplies one unit-weight ambient exception. It does **not** supply the selected-history aggregation of this exception, the reverse sharp Gamma5 pair/cofactor counting dictionary, the nonradial wall payment, a global smooth selected-history mask, the original ordinary-\(J\) comparison, or the PP licence. In particular it does not identify `selectedInnerMass` with `ordinaryBad`, `markedConverted`, or a new mass bearing the same name. The existing 29 H247/native-Wu endpoints are not made necessary manuscript obligations.

## Source selection and verification boundary

The three direct imports are exactly:

- `ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount`;
- `ImbalancedChen.P5U7ActualRoughTargetExclusion`;
- `ImbalancedChen.PowerErrorBudget`.

Select the registered thin-core TupleCount postimage `455fce3476aa7c8230a7afb726a8d02a223bde61`, whose only change from its preceding source is its fibre-core import. This increment leaves it, the fibre core, and the three already accepted radial thin modules unchanged.

The existing target-exclusion supplier has a broad historical import through `P5U7OriginalSourceMass`; its source header is itself `SOURCE_ONLY / UNCOMPILED`. This new module is not presented as a standard-Mathlib-only compilation closure. The full receiving closure has not been reconstructed or qualified here.

When an old owner enters this receiving closure, use the already registered owner postimages from the fibre-core and radial-collar packages wherever the same public declarations have been moved. In particular, a reachable original `Part3DistributionTargets` or `P5zMarkedPrimeFamilyMultiplicity` must be replaced by its existing postimage. Select the corresponding radial owner postimages if those owners are reached. Loading both original and relocated declarations is not permitted. The exact selections and hashes are recorded in `REGISTRY.json`; none of these owners was edited by this increment.

Source identification and independent static mathematical review are complete. The new source still requires actual normal compilation, named kernel replay, full-owned axiom review and source/output binding. No verification credit is inferred from a related old object or from the review.
