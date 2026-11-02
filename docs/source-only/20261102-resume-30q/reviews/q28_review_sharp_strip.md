# Q28 independent review: actual Gamma sharp rejection

Reviewer: `/root/q28_review_sharp_strip`. Static source review only. Review basis includes Q BRIEF, the three P Gamma REPORTs, the P geometric-separation REGISTRY, P `t27_review_gamma.md`, and the original manuscript and completion/low-rank notes. The original mathematical passages and P review were inspected before the new source. No Lean/Lake/compiler, Git, numerical replay, finite guard, author-file edit, or child agent was used. All source candidates remain uncompiled, kernel verification absent, formal credit zero; guards UNEVALUATED.

`PASS` means only the stated source/reuse claim survives this review. `HOLD` means the broader supplier or application is not established here. Neither verdict is build or kernel acceptance.

Abbreviations: `Q17/` = `docs/source-only/20261102-resume-30q/gamma_sharp_strips/`; `Q16/` = the adjacent `gamma_lower_rejected/`; `Pgeom/` = `docs/source-only/20261102-resume-30p/gamma_geometric_separation/`; `M/` = `docs/source-only/20261102-resume-30m/gamma_short_fibre_bv/`. `U` and `O` below mean Q17 `P2GammaUpperStripPayment.lean` and `P2GammaOrderingStripPayment.lean`, respectively.

## Disposition

| Scope | Verdict | Exact boundary |
| --- | --- | --- |
| Existing fixed-order divisor moments | PASS | Concrete native pointwise, ordinary and reciprocal means; no shifted-correlation or Gamma estimate assumed. |
| Actual upper-product strip after the bounded signed modulus sum | PASS | Literal root-label multiplicity, strict complete product below N, exact coprime mean, one fixed mesh. |
| Actual strict-order label count and kernel energy | PASS | New finite injection/count and positive-difference fourth moment are implemented, not hypotheses. |
| Entire original mother-list upper/order remainder | PASS | Same rho, actual aggregate rejection, one N threshold before every later marked pair and arithmetic/grid choice. |
| Treating P rejection support alone as payment | HOLD | Support was insufficient; the new U/O arithmetic proofs are what discharge these two residuals. |
| An outside marked-pair sum or normalized positive-family count licence | HOLD | No such aggregation or Theta comparison is supplied by Q17. |
| Complete Gamma / same-rho PP / H or h count licence | HOLD | Retained distribution, actual family assembly and normalization remain separate; local rejection payment does not discharge them. |
| Inferring arbitrary-log sharp signed BV from fixed-precision smooth approximation alone | HOLD | The original text has different quantifiers and expressly excludes arbitrary signed sharp coupled domains. |

## 1. The moment suppliers are actual source bodies

The inspected native source is
`//wsl.localhost/Debian/home/slava/codex-lean-ve/native-packages/goldbach/MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvryDivisorMean.lean`.

* Lines 104-134 prove `fouvryTau_mul_le`, `fouvryTau_sq_le` and `fouvryTau_pow_le` from the prime-power multichoose inequality and multiplicativity. No squarefree restriction occurs.
* Lines 209-253 prove the reciprocal mean; `sum_fouvryTau_div_le` is at 239-242. Lines 289-350 prove the ordinary mean by the hyperbola identity and harmonic bound.
* `sum_fouvryTau_pow_le_real` at 353-362 gives every fixed integral moment. `sum_alpha_sq_le_fouvryTau` at 377-388 proves the dominated finite coefficient second moment. The zero-th moment is restricted to positive integers; no tau(0) value is used to pay a zero target difference.

The actual source binding is M `P2OriginalGammaDivisorNorm.lean:113-137`: the map into ordered factors retains the fixed old pair as one factor, every word position and the positive quotient. It proves a fibre cardinality bound, rather than pretending the product map is injective. Lines 162-178 group the actual label count, and 217-226 prove `original_Gamma_word_square_sum_le`. The quotient 1 remains admitted. Repeated mother words are separate list occurrences at lines 180-189.

Thus Q17 does not assume a desired strip/HBV estimate or an abstract energy bound. The native and M sources have been read, not merely inferred from theorem names. This is source evidence, not transitive kernel certification.

## 2. Upper-product payment

**PASS.** U:30-82 defines the actual complete-integer strip
`S = {m : 1 <= m < N, N-m <= Y}` and injects it into positive differences `Ioc 0 floor(Y)`. It proves `card(S) <= Y` and

```
sum_{m in S} tau(N-m)^2 <= Y (1+log N)^3.
```

The strict `m<N` comes from the literal source, before any divisor bound. In particular `m=N` is not assigned a fictitious tau(0) cost. U:94-162 first expands the same signed `wordError`, invokes Pgeom `P2GammaCompleteProductTrimPayment.lean:83-114`, and groups the nonnegative majorant by the real source fibre. The original kernel remains progression minus the q-coprime mean. The mean is bounded separately by `4(1+log N)` for positive `Q subset Icc 1 N` and `|rho(q)|<=1`; it is not replaced by an unrestricted mass identity.

Writing `L=1+log N`, `a_m=card(rootProductFiber N t cs m)` and `b_m=tau(N-m)+4L`, U:174-223 derives

```
sum_S a_m^2 <= N L^J,
sum_S b_m^2 <= 34 Y L^3,
|wordError| <= u N L^J + 34 Y L^3/u       (u>0).
```

The constant 34 includes the exact mean: `(tau+4L)^2 <= 2 tau^2+32L^2`, followed by `card(S)<=Y` and `L>=1`. The source moment exponent satisfies `(length(cs)+2)^2-1<=J`; it is fixed before accuracy and arithmetic choices. U:227-239 proves the actual wall implication `N < m exp(4 delta)`, `m<N` => `N-m <= 4 delta N` from `exp(-4 delta)>=1-4 delta`.

U:243-342 chooses

```
B_upper = J+2A+7,
u = (log N)^(-(J+A+2)),
Y = 4 N (log N)^(-B_upper).
```

The two contributions are bounded by `(2^J+1088) N/(log N)^(A+2)`. Both `1<=Y<=N` and absorption of this fixed constant into `eta N/(log N)^A` are proved with existing log/power limits. No `N^epsilon` loss is multiplied into a logarithmic width. U:368-403 attaches the actual trimmed upper rejection, using Q16's nonnegative aggregate weight bound, rather than charging each grid cell separately.

## 3. Strict ordering: implemented count, multiplicity and full kernel moment

**PASS.** O:25-50 proves `closeFollowers_card_le` through the injection `q -> q-p`. Since the original condition is strictly `p<q<(1+e)p`, this positive integer difference is at most `floor(e p)`. Hence there is no additive `+1` rounding term and no retained equal-prime diagonal to pay in this particular source.

O:54-82 proves `card(closePairs N X e)<=eX`: for an actual pair with `pq<=X`, the first coordinate is at most `sqrt(X)`, and summing the follower bound gives at most `e floor(sqrt X)^2`. O:84-117 places the pair beside `orderedFactors(k-1,r)` for the remaining product r and invokes the native reciprocal mean to obtain

```
card(orderEnvelope N k e) <= e N (1+log N)^(k-1).
```

This count is attached to real labels. O:123-222 encodes a label as its first two primes and `drop 2 word ++ [quotient]`. Strict original `Pairwise (<)` makes any close later prime force the second prime to be close. The proof keeps positivity of the fixed old pair d and the complete product `d*p*q*r<N`; dropping d only enlarges the envelope. O:224-267 proves injectivity by recovering the two leading slots, the remaining ordered list and its final quotient. It does not deduplicate equal complete products or remove quotient 1. O:269-281 separately proves the ordering strip empty for words of length at most one.

**PASS.** O:297-370 proves the actual-label kernel energy, with

```
E = max(J+2,15),
sum_{original labels x} [tau(N-m_x)+4(1+log N)]^2 <= 34 N (1+log N)^E.
```

The fourth moment is the native order-two, exponent-four theorem after the positive injection `m -> N-m`; its logarithmic exponent is 15. If `a_m` is the actual fibre cardinality, the proof uses `2 a_m tau(N-m)^2 <= a_m^2+tau(N-m)^4` and the integer inequality `a_m<=a_m^2`. The additional two logarithms of the mean are included in E. A shifted divisor correlation is not a premise. Both moment orders remain fixed as A varies.

O:374-436 combines the proved label count and energy with the literal signed modulus sum:

```
|wordError_order| <= u e N L^(length(cs)-1) + 34 N L^E/u.
```

This is the Young form of the intended square-root-width saving. The originally proposed extra power-saving lattice term is unnecessary for these strict labels: the positive-difference injection removed that term exactly. This observation does not license weak ordering or a source containing equal leading primes.

## 4. One B, actual rejected weights and the full finite mother list

**PASS.** O:438-470 constructs the real trimmed `rawOrderRejectedWeight`, proves its norm at most one, and derives membership in the actual counted strip from U:501-551. This consumes the original legality proof to retain `head<tail`; P's weaker standalone support alternative alone was not enough.

O:474-531 proves `0<=exp(2 delta)-1<=4 delta` once `delta>=0` and `2 delta<=log 2`, then supplies the entire logarithmic ledger. With `l=log N`, it takes

```
E = max(J+2,15),
B_order = J+E+2A+4,
u = l^(E+A+2),
0 < delta <= l^(-B_order).
```

The inequality `length(cs)-1<=J` is derived at 494-497. Thus the count and kernel terms total at most
`(4*2^J+34*2^E) N/l^(A+2)`. O:536-611 chooses one threshold for the exponential-width condition and the final two-log absorption, handles short words by an actual zero proof, and supplies the actual word estimate. The positive-delta gate is retained.

U:407-476 and O:613-665 use `listMomentOrder`, a symbolic maximum over the literal `originalMotherOccurrences` list, and error share `eta/(list.length+1)`. No numerical guard or occurrence count is evaluated. List induction preserves repeated colour-word occurrences. O:667-708 proves that the paid remainder is literally Q16's remaining upper/order term, with the same trim, labels and rho. O:710-742 proves `B_upper<=B_order`, converts the common mesh in the correct direction, and combines the two estimates with half budgets.

The exact final quantifier order at O:719-727 is:

```
A, eta>0 fixed;
eventually N;
every t in pairSupport N;
every Q, rho, T, H, delta, K;
Q subset Icc 1 N, |rho|<=1, 0<delta<=logMesh(B_order,N).
```

Only after the threshold are t, words, moduli, signed rho, trim/grid data and mesh values chosen. The same rho occurs throughout the mother list and in count and mean. This establishes all original mother occurrences at each later t, not an outside sum over t or every arbitrary smooth Gamma amplitude.

Q16 `P2GammaLowerRejectedPayment.lean:50-81` supplies the actual aggregate rejected-weight bound `0<=weight<=1` from the partial nonnegative hat partition. Therefore neither U nor O pays a `K^2` factor. The B above covers every local upper/order error, including multiplicities and the mean. Pgeom's retained-row Abel budget `log(N)^(3B+2)` is a separate retained-distribution cost: the requested local conductor accuracy must be selected after B. It must not be multiplied back into the already aggregated rejection estimate. Q17 does not perform that final conductor composition.

## 5. What is necessary in the original proof, and what is stronger

**PASS — the source distinction.** Pgeom `P2GammaRetainedInteriorGeometry.lean:267-310` chose an exact sharp retained-plus-rejected reconstruction. If that particular source reduction is used, its rejected term needs an actual modulus-summed payment. Q17 now supplies its upper/order part; Q16 separately supplies the enlarged lower part under its complete-product cutoff conditions. These are meaningful actual-source deductions, not a proof of an invented generic HBV port.

**HOLD — do not read the original manuscript as claiming full sharp signed BV.** The pinned manuscript at 258-278 states PP for fixed finite smooth original-prime families with fixed polylogarithmic geometric bounds and the same rho. Lines 332-357 retain the smooth chart and expressly exclude arbitrary signed sharp coupled domains. The completion note at 25-32 and 66-70 has the same limitation. The low-rank note at 132-148 still requires approved separation, complete scales and charged coefficient norms.

Manuscript 554-559 instead uses positive smooth outer approximation at each fixed precision, with N tending to infinity before the approximation error tends to zero. Lines 1481-1489 repeat that order to obtain the final limsup bad-mass bound. That argument requires an actual permitted positive majorant, its limiting mass error, the same licensed rho within each precision, and the corresponding smooth distribution/density supplier. It does not require a theorem for all signed sharp coupled weights at arbitrary logarithmic precision. Q17's absolute local strip payment is a sufficient strengthening for the chosen exact-source route; its previous absence was not a counterexample to this smooth positive route. Fixed-precision convergence alone still does not imply the stronger logarithmic-mesh claim.

**HOLD — uniform fixed t is not a positive-family licence.** Manuscript 803-806 explicitly describes H/h estimates averaged over the positive marked family, not pointwise in B and not for a signed outer measure. I `switched_group_capacity/P2OriginalU5ExactNormalizedSource.lean:76-84,89-112` retains the physical singleton Theta and leaves the actual source prime test to be bounded. Q17 gives an absolute `N/log^A N` error at each t; multiplying this by an uncontrolled number or mass of t values is not justified. No arbitrary outside marked-family sum, relative cell/Theta error, or uniform normalized count licence is proved. A joint actual-label aggregation with its real weights, or the original positive smooth-majorant route, remains a separate supplier. Consequently no `hdensity`, `hLower`, `hUpper`, or P6.3 final-transfer premise is eliminated by Q17 alone.

Difficulty classification: the implemented upper/order reductions are category (2), omitted deductions now supplied in strict source form. Their elaboration/API status remains category (1), untested. The possible category-(3) issue is the unsupported *inference* from fixed-precision smoothing to a stronger sharp signed claim; no contradiction in the manuscript's stated smooth positive argument is established. A limitation of the current fixed-t source model must not be relabelled a manuscript counterexample.

## Static source pins

| File | SHA256 |
| --- | --- |
| Q17 `P2GammaUpperStripPayment.lean` | `6cd9eef12cac6b24fac5147223aec22906bb50adbde83b13ac7b3ca4d19e9ab1` |
| Q17 `P2GammaOrderingStripPayment.lean` | `6a05ca9be0f5f7004d7ae798b342bfa6416332d80f37da4952869cbc65f9ac0f` |
| Q17 `REPORT.md` | `649d0768c923e8b4af33b835f6435a5a7215dc1bbcf1e96ef8372412b1a4402d` |
| Q17 `REGISTRY.json` | `8c3009b873a618ce1f52f7eabeab0e0141fb24e1457d5b57537e6719c390fa39` |
| Q16 `P2GammaLowerRejectedPayment.lean` | `6ece8e845343b640b37189d228c4ee938155bf16d099ca648592443025249c6a` |
| Native `LiLiuPrereqFouvryDivisorMean.lean` | `4e119e53ec5df626bb7e02aa44bf950dbe721bd1f2767fba5fbf90c30784ff59` |
| M `P2OriginalGammaDivisorNorm.lean` | `f9696bad18970592465f84146daa65ef8e72bb8cad11a43645298776709a98df` |
| Pgeom `P2GammaCompleteProductTrimPayment.lean` | `6876350ce5144736ea6d5fb762df0f94683077a1fd60a2a8475fc24e4ba509f7` |
| Manuscript `manuscript-body.tex` | `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` |
| `low-rank-convolution-bv-20261010.txt` | `88edfb5f605e65ad7f05a702a963b5dff1b21f0b4e757edbf4eaed304f4e8f56` |
| `distribution-prime-product-completion-20261010.txt` | `a953b3233c1249b4791830da33b76a58b19ca110a5e1b5b6172b3248a00053e1` |

**PASS — final metadata and claim boundary.** Independently checked all 24 registered file/hash records (including repeated direct-import pins), all 80 declaration locations (55 new public declarations and 25 reused declarations), the three direct import lines, and both new file sizes/line counts. No mismatch remains. U is 554 lines/26328 bytes; O is 745 lines/35941 bytes. The final U log-positivity hypothesis and O's explicit natural-product positivity and multiplication-monotonicity proofs at 170-197 were reread after their API edits. U's four helpers used by O are public declarations in the reviewed bytes. The lexical scan of both new Lean files found no `sorry`, `admit`, `axiom`, `native_decide`, `run_meta`, `run_tac`, `unsafe` or `#eval`. REPORT and REGISTRY correctly exclude the outside t-sum, Theta normalization and full PP. Their pre-review administrative `AWAITING_FINAL_METADATA_CHECK` field is superseded by this independent check; it was not edited by the reviewer.

Final disposition: **PASS** for the actual fixed-t, complete-mother-list upper/order rejection supplier described above; **HOLD** for the outside positive-family/Theta application and entire Gamma/same-rho PP closure. No estimate receives credit merely because it is a premise of a consumer theorem.
