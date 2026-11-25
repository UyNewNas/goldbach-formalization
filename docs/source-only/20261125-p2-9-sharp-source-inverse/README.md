# P2.9: inverse of the original sharp Gamma5 source

Status: **SOURCE_ONLY_UNCOMPILED**, with **0 formal credit, 0 kernel credit and 0 endpoint credit**. The source and documents are Git blobs only. No accepted or queued source was modified; no build, cloud task, commit or ref update was started by this increment.

## The exact missing finite dictionary

The new module is `ImbalancedChen.P2FiniteMarkedGamma5SharpSourceInverse`. It adds one theorem, `raw_source_inverse`.

Given the original data

- a positive integer prefix product `d`;
- two fresh coordinates `qs : Fin 2 → ℕ`, each prime and coprime to the target `N`;
- prime tail coordinates `rs : Fin r → ℕ`;
- every original `raw N Q d qs rs g` for `g ∈ program r`,

put

\[
 l=[q_0,q_1],\qquad L=\operatorname{List.ofFn}(rs),\qquad m=\prod L.
\]

The theorem proves all three conclusions:

\[
 l\in\operatorname{badLabels}(N,Q,d),
\]
\[
 m\in\operatorname{roughNumbers}
       \left(\frac{N}{d\prod l},\operatorname{cutoff}(Q,d,227/50)\right),
\]
\[
 m.\operatorname{primeFactorsList}=L.
\]

These are the original `badLabels`, `roughNumbers` and `cutoff`, not replacement carriers or a new mass definition. The target memberships and canonical factorization are conclusions, not input hypotheses. The old prefix product `d` is passed unchanged. Its full list of old coordinates is not reconstructed by this pointwise theorem.

No separate hypothesis `0 < N`, `0 < Q`, `1 < Q/d`, source-rank bound, plateau property, mass estimate, or distribution statement is needed. Fresh-prime coprimality is the literal original `primeWindow N` requirement. It is not inferred from geometric inequalities.

## Exact geometry and endpoints

Every gate is the existing `P2FiniteMarkedGamma5LogExtension.raw`, and membership in the existing program is discharged through `mem_program`.

| Original gate | Literal condition used by the inverse |
| --- | --- |
| Fresh lower cutoff | \((Q/d)^{a_0}\le q_i\) |
| Fresh upper cutoff | \(q_i<(Q/d)^{a_2}\) |
| Pair order | \(q_0<q_1\) |
| Bad wall | \(Q\le d q_0^2q_1\), including equality |
| Tail roughness | \((Q/d)^{a_0}\le r_i\) |
| Active tail order | \(i<j\Rightarrow r_i\le r_j\) |
| Complete ordinary cap | \(d q_0q_1\prod_i r_i\le N\) |

The tail floor is the original Gamma5 cutoff \((Q/d)^{a_0}\). It is not replaced by the auxiliary \(N^{a/2}\) floor used in the separate target-divisor payment.

The tail may be empty. Then \(m=1\), and the original inclusive rough carrier retains the unit cofactor when the complete product fits. Repeated tail primes are allowed because the tail order is non-strict. The fresh pair is strictly ordered as in the original pair carrier. There is no additional tail coprimality, tail distinctness, or cross-block distinctness assumption.

## Proof supplies reused

The fresh pair is recovered with the original `secondFunctionalMother_tuple_mem` and `mem_primeWindow` characterizations. `original_cutoff` supplies the exact \(a_0\) conversion, and the existing \(a_2\) definition gives the exact upper-cutoff conversion. `badPair` is evaluated on the two original list positions.

For the cofactor, all entries of `List.ofFn rs` are positive primes. The complete raw cap is rewritten as \(d\,l.prod\,m\le N\), and the positive denominator permits the original real quotient bound. The already supplied

`ImbalancedChen.Part5OriginalH430ClassicalFixedClampGeometry.prime_divisor_floor`

gives roughness of the product from the original floor on its listed prime factors.

For the canonical tail, the fixed Mathlib theorem `List.pairwise_ofFn` converts the active tail-order gates into the nondecreasing list order. The proof then uses the existing

`(Nat.primeFactorsList_unique rfl primes).eq_of_pairwise' ...`

with `Nat.primeFactorsList_sorted`, exactly the method already used in the classical fixed-clamp inverse. Its result is reversed to the required `m.primeFactorsList = List.ofFn rs` direction. No general factorization or list-uniqueness theorem is reproved.

## Exact original sources and deduplication

All original project suppliers were read at immutable blobs:

| Supplier | Git blob |
| --- | --- |
| `P2FiniteMarkedGamma5LogExtension` | `d77be7de024ec574ac5c53dae627a093c34ce0e2` |
| `P2EnhancedBadGamma5ArithmeticGeometry` | `dfd20b345e55f6a5820a6facf300d6c739cd867d` |
| `P2EnhancedSwitchedUnsiftedSource` | `e304f1bf084f0ce92e54d986cfd000dbb775fa96` |
| Classical inverse prototype `Part5OriginalH430ClassicalFixedClampPrimeGeometry` | `3d8aab5fb8226c57802f1f95af3033f6f7ad4e17` |
| Existing forward actual plateau `P2FiniteMarkedGamma5ActualPhysicalPlateau` | `74a9d36c43738cd7addae03133e04f7cab57b839` |

`LogExtension.actual_raw` and `actual_source_one` already prove the forward direction on original sources. The actual rank and physical plateau consumers also run forward and are left unchanged.

The classical `tuple_mem` theorem already contains the sorted-tail inverse method, but its carrier is the Gamma9–21 classical target-1 source. Its inverse fresh windows explicitly use `Nat.coprime_one_right`. It cannot be cited as an existing Gamma5 target-\(N\) result. This new theorem connects the existing methods to the exact original Gamma5 predicates.

The original active and source-only inventories at `a929011ec95843553fc2e10b7291c8077e0952c0`, the relevant T21/T23 and actual-rank/plateau sources, and the P2.9 additions through `913a205` were checked. No matching Gamma5 reverse source theorem was found in that inspected scope. Default-branch code search is not treated as evidence of absence.

## 1106 manuscript role

The frozen manuscript is `UyNewNas/chen-imbalanced-semiprimes` at `a988cba584d803ae2856a0de50efb582f4f3dd6a`.

- `paper/release-20261106/en/sieve-appendix.tex`, 634–660, defines the positively marked pair/rough-cofactor source and the Gamma5 summand with \(q_1<q_2\) and the original \(R^{a_0}\) rough threshold.
- The same file, 763–776, keeps the bad Gamma5 region inclusive at its equality wall.
- `paper/release-20261106/en/argument.tex`, 359–407, requires the actual ordinary mass of the admitted family and positive outer approximation before the prime-product consequence.
- `paper/release-20261106/en/sieve-appendix.tex`, 1090–1101, fixes the finite query family and positive cutoff before \(N\) increases.

This increment fills a finite-expression and canonical-factorization connection for the original discrete source. It is not a new analytic premise or a claim that the manuscript separately states this exact Lean theorem.

## Remaining scope and import boundary

The three direct imports are:

- `ImbalancedChen.P2FiniteMarkedGamma5LogExtension`;
- `ImbalancedChen.P2MarkedPrimeDivisorFloorCore`;
- `Mathlib.Data.List.OfFn`.

The logarithmic extension selects the existing same-FQN `LogProfileCore` and the old arithmetic Gamma5 suppliers. Their broad receiving closure is not qualified by the acceptance of the thin geometric/Euler modules. The prime-divisor floor theorem is selected from the already existing thin core; if the original classical geometry owner is also reached, select its previously registered owner postimage to avoid duplicate public declarations. No owner is edited here.

This theorem is pointwise. A subsequent finite transport must still preserve each original occurrence and old-prefix list, prove injectivity across canonical tail lengths and split indices, and reindex the original marked sums. The noncoprime ambient payment is a separate source increment. Nonradial smooth excess, the global selected-history mask, the original ordinary-\(J\) comparison, and PP remain outside this theorem. No 29-endpoint H247 necessity claim is introduced.

Independent static review checked the exact 108-line source, including the cutoff constants, both list positions, inclusive bad wall, denominator positivity, canonical-tail orientation, empty tail and repeated primes. Compilation, named kernel replay, full-owned axiom review and coherent source/output binding remain outstanding for this new module.
