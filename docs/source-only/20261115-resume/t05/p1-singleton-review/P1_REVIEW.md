# T05 independent review of T06 singleton rough-prime correction

Decision: **PASS at the mathematical source/contract level for the exact frozen six-theorem file.** No source edit is requested. This review does not certify elaboration, kernel replay, transitive axioms, the full P1.4 target, Y07/Y08, or the remaining prime-product estimates.

The reviewed T06 `FREEZE.json` has SHA256 `180097e0f89348cef0508f0242cb865d6a3a9ef23c5fcb703c27861d3941ce8a`. The new file `P1OriginalSingletonRoughPrimeReserveZero.lean` is 8779 bytes, SHA256 `6a4c45ac6215d3b697e7612330183150fbe6337b3cbb835e819f11fb61ab4e97`, Git blob `e30e4a24443ff78f60863872c2062505a916cf11`. All 17 frozen artifact identities were independently recomputed. Seven relevant existing sources were additionally checked against their actual immutable Git trees: the two direct imports, four key profile/licence/correction/strict-rough sources, and the original final-parameter schedule. All match; see `P1_FREEZE_BYTE_AUDIT.json`.

## Original object and necessity

The original prime-product argument, `distribution-prime-product-completion-20261010.txt:23–32,72–105`, has a true original smooth prime floor and fixes the chart rough cutoff before HB. Its line 89 says original primes eventually exceed that cutoff. `lichtman-current-upper-density-assembly-20261009.txt:299–334` fixes the policy, rank and smoothing parameters before the physical target grows. These are the necessary facts specialized here; no arbitrary arithmetic filter or desired PP inequality is added.

The existing `P1OriginalSingletonMiddleTensor.singletonAtlas` is literally

\[
\operatorname{trimReserve}
+\sum_{j\in\operatorname{chartBank}(2N,1)}
 (\operatorname{mediumAtlas}+\operatorname{noMediumAtlas}
  -\operatorname{properPowerReserve}+\operatorname{roughPrimeReserve}).
\]

T06 rewrites this actual object. The licence is `actualLicence kappa 6 P.N`, the complete modulus set is `products P`, and the signed coefficient is `fun d => (free P d : ℂ)`. They are not replaced by a generic Family or a coefficient envelope.

The old singleton HB sources still retain the rough-prime term. The existing generic `family_rough_reserve_zero` needs its own admissible-Family support inequality; it does not itself identify this actual singleton licence. The existing upper-pair rough-zero source uses a two-prime outer-ramp licence, and `Part5OriginalH430ClassicalRoughFloor` uses another marked family. They are useful preceding patterns, not an already proved identity for this singletonAtlas. The new source reuses the existing cutoff and rough-word lemmas rather than reproving those results. Actual member supply and OneLong were not re-reviewed or counted as new work.

## Precise cap and profile check

The actual source enumerates `primeTuples (2*N) 1`; its physical profile, moving residue and trim target remain N. `actualLicence` itself is the ambient licence for `profile (1-kappa) (logWidth B N) N`, not a change of physical target. The licence's `integerExtension` is exactly that ambient profile on integer coordinates. `listExtension_ofFn` and `ofFn_wordVector` convert the original singleton word to the same vector without permuting or filtering it.

`logWidth_bounds B hN` really states `0 < logWidth B N` and `logWidth B N <= 1` for N>=2, including B=0. The actual `profile_support_short` then gives

\[
N^{1-\kappa}<p<N(1+\delta),\qquad0<\delta\le1.
\]

The source uses its strict lower floor and the original prime-tuple cap p<=2N. Thus the upper collar p>N remains present. It is not silently cut off at N. This extraction uses no derivative bounds, so the support conclusion is uniform in B even though more general analytic estimates for the profile fix B beforehand.

The first theorem's `primeTuples_spec` projections match the real declaration: word length one, and for each member `Prime p ∧ 1<=p ∧ p<=cap`. The `wordVector` and `List.ofFn` identities are genuine existing declarations. The complex coercion/nonzero extraction in `actual_singleton_chart_windows` also matches the actual factorization:

`originalChart = tupleProfile * (eta * (listExtension : ℂ))`.

Nonzero chart value therefore supplies both the original tupleProfile and the original licence value as nonzero. `profile_nonzero_support` gives the original same-word `List.Forall₂` psi windows; no rough chart or per-coordinate replacement is introduced.

## Doubled-cap inequality and cutoff

For fixed kappa<1, define a=(1-kappa)/2>0. For N>=2,

\[
2N\le N^2,
\qquad (2N)^a\le (N^2)^a=N^{1-\kappa}<p.
\]

The source's real-power monotonicity and multiplication rules have the required nonnegative bases and exponent. The two natural-to-real casts are correct. This only changes the ambient cap supplied to the existing cutoff theorem; all occurrences of the physical profile and `wordKernel` still use N.

The exact repaired supplier is `independent_test_chart_cutoff_eventual` from the source selected at commit `b6079159c2af12cb5c67a0055ef1db9d1e60f072`, SHA256 `d849269829a19b3b733082a0fe54291b0f920cc752ec900469cd49b3c8cd17c1`. Its actual type chooses one threshold after K and a, then works for every 1<=k<=K and every original chart/word with the same psi windows and source bounds. Its proof controls the original scalar argument between a growing lower bound and `2^(8K+2)*cap^K`, then uses the existing subpower envelope. I read that proof route and its actual strict conclusion, not just a theorem-name match.

T06 instantiates this supplier at cap=2N, k=1, and the same js and ps. The selected threshold is `max 2 M0`, which implies both N>=2 and 2N>=M0. Hence

\[
\operatorname{beforeHBCutoff}(K,js)<(2N)^a\le p.
\]

`beforeHBCutoff K js` is exactly `chartCutoff K (scales js)`. It has not been reset at an HB rectangle or a future slot. Applying the bound separately to each prime word is a proof of the same fixed chart cutoff, not a new cutoff depending on that word.

## Exact-zero mechanism and quantifiers

The actual correction is the finite sum

\[
\sum_{ps\in\operatorname{primeTuples}(2N,1)}
 \operatorname{originalChart}(L,N,\kappa_0,js,ps)
 \bigl(1-\operatorname{roughWord}(\operatorname{beforeHBCutoff}(K,js),ps)\bigr)
 \operatorname{wordKernel}(Q,\rho,N,ps).
\]

If the chart value is zero, the summand is zero with no scale assumption. Otherwise the actual prime floor and cutoff comparison give strict prime>cutoff. The existing `roughWord_one_on_prime_word` therefore gives roughWord=1, again making the summand exactly zero. Empty carriers and inactive charts are handled by finite sums and zero factors, not discarded by an unstated nonemptiness assumption.

The theorem quantifier order is correct: fix K>=1 and kappa<1, choose N0, then quantify over N>=N0 and all B,kappa0,Q,rho,js. Neither N0 nor the cutoff supplier depends on B, Q, rho, kappa0 or a subsequently chosen chart. K and kappa cannot be varied with N under this conclusion.

The unrestricted finite Q and complex rho follow only because their exact kernel is multiplied by zero. No absolute-value rho, cancellation hypothesis, coefficient bound, modulus restriction or coprimality assumption is needed for this local identity. This universality does not assert arbitrary-Q/rho prime-product distribution. For the same reason this local identity permits B or kappa0 to be chosen after N; it does not extend the quantifier order of separate smoothing or PP estimates.

The chart-sum theorem is a direct finite sum of these identities. The final theorem unfolds the already defined singletonAtlas, specializes B=6 and the original products/free coefficient, and removes only the final `+ roughPrimeReserve`. It keeps trimReserve, mediumAtlas, noMediumAtlas and the negative properPowerReserve with their original signs and domains. The source does not set noMediumAtlas or the entire discrepancy to zero.

## Existing schedule and import selection

`P1OriginalSingletonRectangleSchedule.original_single_prime` first fixes its smoothing exponent kap<1 and K>=2, then the original r,n,e,q,a,m,beta,k and error budgets, and only afterwards chooses the target threshold. The new reserve threshold depends only on K and kap. Taking the maximum with that existing N0 preserves every earlier choice and contributes no error. This is a valid way to use the new equality with the existing schedule; T06 does not claim to prove a new full PP or historical-middle estimate.

The two direct imports are exact and must remain selected as follows:

| Module | Commit | SHA256 |
|---|---|---|
| `P1OriginalSingletonMiddleTensor` | `2ba389da45a2b606957394825b674e3f0b8da82d` | `18c8beeb835b6c10b1907afeb06bfddef08def3b668b553183b3fd0f2bef303b` |
| `P5IndependentTestPrimeChartUniformCutoff` repaired source | `b6079159c2af12cb5c67a0055ef1db9d1e60f072` | `d849269829a19b3b733082a0fe54291b0f920cc752ec900469cd49b3c8cd17c1` |

The original profile/licence and correction/strict-rough sources at `32d541884c85748e3fb18f7a83801b2f8b16e359` also match their frozen byte and tree identities. In addition I read the actual declarations for `primeTuples_spec`, `words_spec`, `profile_nonzero_support`, `integerExtension`, `listExtension_ofFn`, `wordVector`, `ofFn_wordVector`, `beforeHBCutoff` and `eventually_subpower_envelope` from the existing source snapshots. This is a direct-import and used-API audit; it does not claim a new recursive closure certificate for the entire P1 graph.

No mathematical or static API defect was found in the six new proof bodies. There is no new assumed desired inequality or hidden policy field. The specific source omission is filled; historical savingMiddle/comparisonMiddle, final medium/two-long/proper-power/trim payments, full signed PP, and same-source elaboration/kernel/axiom checks remain separately open. The exact-source approval is recorded in `P1_ROUGH_PRIME_ZERO_ALLOWLIST.json`; formal credit remains zero.
