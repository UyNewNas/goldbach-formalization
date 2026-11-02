# R17 / D15 — actual joint Gamma upper rejection and the zero-Theta branch

**SOURCE-WRITTEN PARTIAL SUPPLIER; D15 REMAINS OPEN. UNCOMPILED, KERNEL-UNVERIFIED, ZERO FORMAL CREDIT.** The new result pays the upper-product rejection after the entire original marked-pair sum, with no pair-cardinality loss. It also gives an exact product-weight connection to the existing Theta and settles zero-Theta families absolutely. It does **not** pay the complete positive-mass relative-Theta error requested by D15.

Only `docs/source-only/20261102-resume-30r/gamma_outer_theta/` was written. No Lean/Lake/compiler, CI, finite guard, numerical replay, Git operation, production/older-file edit or child agent was used. All inherited finite bodies remain UNEVALUATED. The source declarations, imports and raw-byte hashes are recorded in `REGISTRY.json`; they are static evidence, not successful elaboration.

## Original scope and the boundary that remains

The inspected manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, raw SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.

- Lines 258–278 state the permitted smooth labelled-prime PP error at the same signed rho and exact q-coprime mean.
- Lines 316–357 retain the original smooth chart and complete product scale, charge fixed scalar/chart costs, and exclude an arbitrary signed sharp coupled-domain assertion.
- Lines 543–559 pay the complete-product lower trim and specify positive outer approximation with N tending to infinity at each fixed precision before the precision tends to zero. No division by the family mass is made.
- Lines 795–817 define the common physical-Q normalizer `4 li(N) sum sigma(B) C(BN)/(phi(B) log(Q/B))`. The H/h statement is averaged over the positive marked family. Physical residual and alpha are not recomputed at an auxiliary analytic level.
- `distribution-coefficient-completion-20261010.txt:69–110,234–237` distinguishes physical Q, an analytic cover, and the fixed scalar masses in marked states.

Q16 supplies the enlarged lower rejected error at every fixed t, uniformly in later t. Q17 supplies the complete original mother-list upper/order error at every fixed t. Q27/Q28 accept those bounded source claims but explicitly retain the outside marked-family/Theta obligation. This R packet neither describes those local payments as absent nor multiplies their `N/log^A N` bounds by the number of pairs.

The remaining source issue is precise: the current `rootLabels N t cs` contains the **t-dependent** original `rootQ N t`. A causal selected family with one common physical Q, its nonnegative occurrence weights and its exact connection to the original root/descendant counts still has to be constructed. R11 reported that its prefix-mixture Fubini work does not yet provide this joint Gamma/selected-history dictionary. R18's chosen-grid costs and R19's actual PP consumers do not supply it either. `pairSourceTheta` below is exactly the existing Theta on a product pushforward; no equality `Qphys = rootQ N t` on a policy-selected family is inferred from that definition.

## New actual joint arithmetic source

`P2GammaJointLabels.lean` imports Q17's existing upper-strip module. It constructs

```
jointLabels N cs = {(t,x) : t in pairSupport N, x in rootLabels N t cs},
jointProduct(t,x) = (t1*t2) * x.word.prod * x.quotient.
```

The finite union is tagged by t. `joint_sum_eq_pair_sum` proves its exact disjoint-fibre sum, and `jointError_eq_outer_wordError` identifies its bounded signed-modulus error with the original outside sum of P's literal `wordError`. The same rho occurs throughout. The word, original masks, strict complete-product ceiling and quotient 1 are retained.

`card_jointProductFiber_le` uses the explicit code

```
[t1, t2] ++ originalWord ++ [originalQuotient].
```

Both old primes are separate slots. Equality of this list recovers t1, t2, the fixed-length original word and the final quotient. Consequently the ACTUAL joint fibre multiplicity `a_m` satisfies

```
a_m <= tau_(length(cs)+3)(m).
```

The complete-product map is not asserted injective. The old fixed-t source used order `length(cs)+2` because the old product was one fixed factor. That order cannot simply be carried over to the joint source. The extra slot is explicitly paid here.

The native unrestricted fixed-divisor second moment, read from the exact accessible source, gives

```
sum_{m in S} a_m^2 <= X (1+log X)^((length(cs)+3)^2-1),
S subset (0,floor X], X>=1.
```

This is the new actual `joint_multiplicity_square_sum_le`. It has no coefficient-energy or fibre-count premise. M's `orderedFactors`, `mem_orderedFactors`, `card_orderedFactors` and the native divisor mean are reused unchanged. No new number-theoretic moment theorem is claimed.

## Upper-product rejection after the full outer sum

For `L=1+log N`, `J >= (length(cs)+3)^2-1`, `u>0`, `1<=Y<=N`, and a one-bounded weight on the literal joint labels supported on `0<N-m<=Y`, the new finite theorem proves

```
|jointError| <= u*N*L^J + 34*Y*L^3/u.
```

The proof expands the actual common-rho kernel before taking absolute values, groups by the complete integer, and uses the new joint fibre second moment. Q17's already supplied injection `m -> N-m`, short-difference divisor moment, band cardinality and scaled Young inequality are reused. The coprime mean is retained and costs its existing `4L`. The strict source ceiling gives `m<N` before any divisor of `N-m` is used. The `m=N` fibre is proved empty when extending the product sum; no `tau(0)` payment is inserted.

`P2GammaJointUpperPayment.lean` attaches this result to Q17's **actual** `wordUpperRejectedWeight`, including the smooth trim, aggregate hat rejection and first-priority lower split. Its range and strict upper-wall support are consumed from Q17; they are not fresh hypotheses about an unknown residual. The rejection is already aggregated over the grid, so there is no K² loss.

Let `J` be the symbolic maximum of `(length(cs)+3)^2-1` over the original mother OCCURRENCE LIST. Define

```
B = upperMeshExponent J A = J+2A+7,
delta <= (log N)^(-B),
u = (log N)^(-(J+A+2)).
```

The Q17 numerical balance gives `(2^J+1088) N/(log N)^(A+2)`. Two further logarithms absorb any fixed positive tolerance. Q's numerical helper is private, so its elementary balance is restated as `joint_log_budget`; this repeated scalar calculation is declared reuse and is not counted as a new analytic supplier.

`originalJointUpperError_eq_outer` proves exactly

```
originalJointUpperError
  = sum_{t in pairSupport N} sigma(t) * originalUpperRejectedError(N,t,...).
```

Repeated mother words remain separate list occurrences. The proof allocates `eta/(list.length+1)` without evaluating a mother count, maximum or guard. The final theorem `eventually_originalJointUpperError` places A, eta and B before ONE N threshold, and then allows every modulus set, same signed rho, selector `0<=sigma(t)<=1`, trim/grid parameters and permitted width. It concludes the **absolute** bound `eta N/(log N)^A` on the entire outer sum.

`eventually_originalJointUpperError_height` permits any fixed scalar height `C>0`, chosen before N, with `0<=sigma(t)<=C`. It proves exact homogeneity, applies the preceding theorem to `sigma/C` with tolerance `eta/C`, and restores the scale. No bound on the number or total mass of selected t values is required. The actual causal policy's scalar-height supplier is not claimed here.

## Existing Theta, actual product weights and absolute zero mass

`P2GammaPairThetaZero.lean` directly reuses production `P5PrimePairEndpoint.productImage`, `productWeight` and `productWeight_sum`. It defines

```
pairSourceTheta N Qphys sigma
  = Theta N Qphys (productImage(pairSupport N))
      (productWeight(pairSupport N,sigma)).
```

M's existing `Theta_eq_sum_atoms` then gives exactly

```
pairSourceTheta = sum_t sigma(t) * thetaAtom N Qphys (t1*t2).
```

This retains all equal-product weights, the original singular factor `C((t1*t2)N)`, `phi(t1*t2)`, literal li and `log(Qphys/(t1*t2))`. In particular it does not replace the arithmetic factor by `prod 1/(p-1)`. M's actual inserted-prime normalization has fresh factor `1/(p-2)` and repeated-prefix factor `1/p`; neither is silently altered.

Under the primitive conditions `N>=4`, nonnegative sigma and `Qphys/(t1*t2)>1` on the pair support, the same production `Theta_pos` proves

```
pairSourceTheta=0  iff  every original sigma(t)=0.
```

The positivity argument already appears inside P's `zero_theta_units`; that argument is reused, with a new attachment to this pair-source pushforward. It is not credited as a new analytic zero-mass theorem. Consequently every weighted outside arithmetic test vanishes. `originalJointRejectedError_zero_of_Theta_zero` applies this to the literal Q16 enlarged lower term plus Q17 remaining upper/order term and proves its **absolute** value is exactly zero. There is no division by Theta, no positive-mass assumption and no limiting argument. The earlier original low-product trim is a separate source quantity, not silently included in the definition of this rejected error.

## Exactly what is still open

1. The joint original lower-trim/lower-rejected and strict-order rejected sums for **positive-mass** outside families. Q16/Q17 fixed-t results remain available; this packet only supplies a new joint upper-product payment and the exact zero branch.
2. Actual selected t/mother/mark membership, full labelled multiplicities and scalar weights from the frozen causal policy, including its common physical-Q source identity. Arbitrary finite positive sigma with a primitive height bound is an envelope, not a proof that the requested actual policy is that sigma.
3. The relative-Theta mass/error relation for every permitted positive family, with a threshold in the required order. The absolute `eta N/log^A N` bound does not establish it. No lower bound for Theta, normalized density, comparable mass, or desired relative error has been inserted as a premise of a new consumer.
4. The retained distribution, actual post-loss level and full chart/mother/conductor/same-rho PP application. R18/R19 own their additional parts; this packet does not discharge `hUniformPP`, `hdensity`, `hLower`, `hUpper` or any final yellow node.

For a particular fixed positive geometric family, an independently established asymptotic comparison with the original normalization could convert an absolute logarithmic saving. That comparison and its zero/degenerate cases must be proved from the actual family. It is not supplied here, and mere positivity of Theta is insufficient for a uniform conversion. Likewise, a generic vanishing fixed-precision smoothing error does not yield a moving logarithmic-mesh estimate by itself.

Difficulty: the new joint encoding, finite payment, threshold aggregation and zero-source conversion are category **(2)** supplied source deductions. Their untested Lean/API/elaboration status is category **(1)**. The actual selected-family construction and positive-mass relative-Theta supplier remain category **(2)/(3)** obligations. This is not a manuscript counterexample: the manuscript's permitted positive smooth outer route has narrower claims and its stated quantifier order is unchanged.

## Reuse, hashes and verification

Production, all source-only batches and the ignored `.lake/proof-continuation/source-reviews/drafts` were searched, including a final `--hidden --no-ignore` search for joint Gamma/fibre/outside-rejection identifiers. No existing actual joint upper-rejection supplier was located in the inspected sources. Existing P5 pair pushforward, M divisor/Theta APIs, P zero-mass positivity and Q local residual suppliers were found and reused. The accessible UNC native divisor source was read and hashed; no guessed external definition or unverified web theorem is used.

| New source | Intended module | Raw SHA256 |
| --- | --- | --- |
| `P2GammaJointLabels.lean` | `ImbalancedChen.P2GammaJointLabels` | `b4dfa9d2040cb424978dd5b082191a5d867cef96d9edaf91864c00429dae99b8` |
| `P2GammaJointUpperPayment.lean` | `ImbalancedChen.P2GammaJointUpperPayment` | `74e173684ae2f66833b23a97ccb8969acf5f04ec962ca16bce4a8227cdf00834` |
| `P2GammaPairThetaZero.lean` | `ImbalancedChen.P2GammaPairThetaZero` | `60b8e00ccf7187824decffbe55d9c01d990db4081b3aa899d9e89598d43d370d` |

Direct-import resolutions, reused declaration lines and complete hashes are in REGISTRY. Source-only imports still require materialization at the stated intended module paths. The finite cardinality/list definitions and all tactic proofs have not been run. Static text inspection found no admission, axiom or evaluation/compiler escape in the new Lean files. R29's independent review is recorded separately by its owner; a source PASS, if given, applies only to the bounded claims above and carries no kernel credit.
