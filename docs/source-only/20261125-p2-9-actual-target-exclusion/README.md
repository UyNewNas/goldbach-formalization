# P2.9: target-divisor payment for the original selected-history profile

Status: **SOURCE_ONLY_UNCOMPILED**, with **0 formal credit, 0 kernel credit and 0 endpoint credit**. Only Git blobs are created. This increment does not modify the previously reviewed 638-line radial aggregate, the accepted thin modules, or the TupleCount source currently assigned to the verification agent.

## Actual source and exact finite connection

The new module is `ImbalancedChen.P2FiniteMarkedGamma5ActualTargetExclusion`.

Its `noncoprimeSlice` uses the existing `boundedProfileWeight` on precisely the existing ordered-prime enumerator `Part3.labelledPrimeTuples (k+(2+r)) (2*N)`. It retains a term exactly when the **complete** product is not coprime to `N`. Thus the same old-prefix equality, same physical profile, same coordinate order and same repeated primes are retained.

`selectedNoncoprimeMass` then uses the original finite sums

\[
 \sum_{p\in\operatorname{originalBand}(N,U4)}
 \sum_{l\in B(p)}
 \operatorname{levelMark}(l)
 \sum_{\substack{(k,r)\in\mathrm{Split}\\k+2+r\le K}}
 \operatorname{noncoprimeSlice}
 \left(N,k,r,\log(\operatorname{rootQ}(N,n,U4,t,p)),h,
       \operatorname{current.old}(l)\right).
\]

Every original `p` and dependent `LevelIndex` remains present. The theorem does not replace equal-product histories by one representative.

The public source dictionaries are:

- `noncoprimeSlice_eq_filtered`: removes only zero profile terms, keeping the literal original prefix weight;
- `selectedNoncoprimeMass_eq_cells`: partitions the original root-prime sum into its original `RootCode n` cells and uses the already proved `originalRootCellBand_Q`;
- `selectedNoncoprimeMass_eq_prefix_sum`: rearranges the same finite sums into full tuples with the existing `prefixWeight` coefficient.

The last dictionary is an exact equality for this newly specified noncoprime part of the existing raw profile sum. It is not an equality with `ordinaryBad`, `markedConverted` or `J`.

## The source-level estimate

Let

\[
 C(n)=\operatorname{aggregateCard}(n)
     =\#\mathrm{shapeWords}\,
       \#\mathrm{RootCode}(n)\,
       \#\mathrm{Split}.
\]

This is the already defined constant from `ActualRadialAggregate`; it is not redefined here. Let `noncoprimeCount N` be the previously supplied single-ambient all-rank count at the original frozen cutoff \(\operatorname{cut}(N)=N^{a/2}\).

For \(N>0\), \(0<h\le1/8\), and the intermediate inequality

\[
 \operatorname{cut}(N)\le N^a/2,
\]

the new `selectedNoncoprimeMass_le_count` proves

\[
 \operatorname{selectedNoncoprimeMass}(N,n,\mathrm{dep},t,h,B)
 \le C(n)\operatorname{noncoprimeCount}(N).
\]

The intermediate cutoff inequality is not an added final assumption. The existing `eventually_cut_le_half_floor` supplies it uniformly before the final eventual target.

The support inclusion is derived from `finPhysicalProfile_nonzero_support`. A nonzero original profile has each coordinate greater than \(N^a/2\), and its complete product is less than \(\exp(\log(1+h))N<2N\). Its actual weight lies in \([0,1]\) by `physicalProfile_bounds`. No coordinate support or weight bound is taken as a new target premise.

The already proved `prefixWeight_le_shapeCard` bounds the entire original positive history coefficient at a fixed complete old word. Its proof uses positive `levelMark` and the original occurrence bound; it is not a signed cancellation estimate. Only after using it are the fixed root-cell and split cardinalities charged. The moving root primes and moving history positions receive no individual epsilon allowance.

These fixed factors multiply only the vanishing exception count. They are not introduced as factors on the original sharp ordinary mass or its \(J\) coefficient.

## One threshold for every allowed width and every fixed depth

For each fixed `n` and \(\varepsilon>0\), `absolute_selected_noncoprime_payment` proves

\[
 \forall^\infty N,\quad
 \forall\,\mathrm{dep},t,h,\quad 0<h\le1/8,\quad
 \forall B,\qquad
 \frac{\log N}{N}\,
 \operatorname{selectedNoncoprimeMass}(N,n,\mathrm{dep},t,h,B)
 \le\varepsilon.
\]

The threshold is uniform in the allowed physical width, root parameter, depth and all dependent selected subfamilies. The fixed root precision `n` occurs before this eventual quantifier.

`allDepthSelectedNoncoprimeMass` is the fixed sum over `dep : Fin 431`, with

`B : (dep : Fin 431) → (p : ℕ) → Finset (LevelIndex N n .U4 t p dep.val)`.

The source-level estimate is

\[
 \operatorname{allDepthSelectedNoncoprimeMass}
 \le 431\,C(n)\operatorname{noncoprimeCount}(N).
\]

`absolute_all_depth_selected_noncoprime_payment` gives the corresponding absolute epsilon allowance, using \(\varepsilon/431\) before the moving target and subfamilies. This is one finite remaining-depth error budget. It does not assert that all generations are simultaneous terms of one original counting identity.

The uniformity in \(h\) permits use of a width already fixed by the radial payment. It supplies no new licence to move the approximation precision through a prime-product limit.

## Exact event and remaining scope

The filtered event is `¬Nat.Coprime (completeProduct) N`. It may include a tail prime divisor of `N` that the original Gamma5 rough-cofactor source still permits. The statement is a positive upper allowance for the full-product event, not an equality with the event that only a fresh prime violates `primeWindow N`.

All old, fresh and tail coordinates remain in the same tuple. Zero old rank is retained in the ambient split domain; the existing actual-prefix coefficient vanishes for the empty old word. The new code does not reprove that original fact. Repeated primes and unit tails are retained.

The source has not yet been reindexed bijectively against the original pair/cofactor `ordinaryBad` sum. The separate `SharpSourceInverse` increment supplies only the pointwise inverse. Nonradial wall payment, a global admitted smooth selected-history mask, the original ordinary-\(J\) comparison and the PP licence remain separate. No 29-endpoint H247 necessity claim is introduced.

## Reused sources and selected owners

The two direct imports are:

- `ImbalancedChen.P2FiniteMarkedGamma5ActualRadialAggregate`, exact 638-line source blob `93062adda7fdc87780a9c684c046652c567558d9`, SHA256 `7683ad34324d753af07709b5b1b0f12a77b836c3e07aabb5ec58e808e446c713`;
- `ImbalancedChen.P2FiniteMarkedGamma5TargetExclusion`, source blob `68641a9d05fdd4ceafb60a22656d310e63ee2083`, SHA256 `9b4296b5ee2d5213f07850f49094759b7fed57f9ba2ff9a1ac345bfb3b8de5a5`.

The original shape/occurrence proof and prefix coefficient bound are called without modification. The original cardinal target-divisor estimate and log-power decay are reached through `TargetExclusion` and are not reproved.

The only newly local generic helper commutes a fixed finite sum with the original dependent history sums. The old helper is private to its module. No abstract desired inequality is supplied as a hypothesis.

The current selected TupleCount input is its header-repaired blob `de40d26b7be3b5287e3c4362fee35b73b79f0e74`, SHA256 `b5a80dfe3fa83e17e1e87c1b0bba8b247ae41d4e64f8af0cc0b3c8e3ad306e70`. That supersedes the initial `455fce...` postimage in earlier source registries: its imports and all declaration/proof bodies are identical, with only an unused namespace removed from the header. This increment does not edit that input.

The combined old-history and target-exclusion import closure remains unqualified. Select the existing original-owner postimages recorded by the radial/fibre and history packages whenever an extracted declaration would otherwise be duplicated. Previously accepted thin objects and an old history object tree cannot simply be mixed without coherent source/output binding. The exact current selections and inherited unresolved boundaries are recorded in `REGISTRY.json`.

## Manuscript and verification

The frozen 1106 manuscript is `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`:

- `sieve-appendix.tex` 494–552 fixes the common \(Q\), original slots and finite positive marked families;
- `sieve-appendix.tex` 634–660 retains the same nonnegative marks on the original pair/rough sources;
- `argument.tex` 359–407 gives the positive-product consequence and order of smooth approximation;
- `sieve-appendix.tex` 1090–1101 fixes positive cutoffs and finite queries before \(N\), with absolute errors.

This is a finite positive aggregation of a separately supplied elementary deletion estimate. It is an actual discrete-source connection, not the global smooth-family or distribution theorem.

Independent static review checked the exact 346-line source, its unchanged profile support, prefix dictionaries, fixed coefficients, all-depth sum and final quantifier order. All new formal and kernel credits remain zero pending actual compilation and the required kernel, full-owned and source-binding gates.
