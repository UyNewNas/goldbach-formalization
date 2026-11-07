# Q15 — literal Gamma head/window attachment

Status: **SOURCE-WRITTEN, UNCOMPILED, ZERO FORMAL CREDIT.** The nominated finite head-colour/window attachment is supplied in the new source candidate. The complete Gamma estimate and `P3.6.same_rho_PP` remain OPEN. This packet writes only its assigned Q directory; no old source was changed, compiler/build/CI/finite guard/numerical replay/Git operation or child agent was used.

## Source basis and exact reuse

Read first: Q BRIEF, Q02 reuse inventory, P `gamma_geometric_separation` REPORT/REGISTRY and t27 review. The manuscript at `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:258-278,316-341` has SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. It requires geometric weights on labelled original primes, the same signed rho and coprime mean, complete-product scale and charged separation. This task supplies a finite endpoint dictionary, not a new distribution argument.

The production/source-only/hidden-draft search found no prior literal Gamma-head colour/window attachment. It did find the exact natural/integer bridge in O, as already reported by P t14 and t27. That bridge, P's retained Cartesian identity and O's grid/Abel budget are imported and reused, not rewritten.

The native UNC install is unavailable in this checkout. To avoid guessing definitions or silently substituting another version, the three native files were read through the GitHub connector at fixed `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Hashing the returned UTF-8 content reproduces each Git blob SHA. The mother-carrier raw hash also agrees with the frozen M registry. A local NTFS native-source backup was read for discovery only; the fixed-ref connector reads below are the authoritative native pins.

| Native source at the fixed ref | Raw SHA256 | Git blob SHA1 | Actual definition read |
| --- | --- | --- | --- |
| [SecondFunctionalMotherCarriers.lean](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/SecondFunctionalMotherCarriers.lean) | `9f242487d50a4d1778d6d78a758da9923c39b8a46911ac3be9c0b7a970d0285c` | `32d28cc28471150dea398bc77d2531d8a2434a8a` | Four colours: first successful strict test at b,c,e, then colour 3. |
| [GoldbachWeights.lean](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/GoldbachWeights.lean) | `e66c07695fd9625bde2b9d9f9c53ecb4a84bed7f088dd3cc81b8d2012c2333c6` | `90c187a945e12e0ceec542cb86ab918b671682aa` | `primeWindow N a f` is prime, coprime to N, with `a <= p < f`. |
| [LiLiuFouvryPrimeSW.lean](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuFouvryPrimeSW.lean) | `3e0d3ca450cb29998cdc5942570b929d057905a35cf545f6ffb791020cf3530d` | `3a58b624e3abf603b577c83b419095e7f9c47c40` | `primeSWBeta = 1_Prime`; `primeSWInterval u v = Ioc (floor u) (floor v)`. |

## New finite dictionary

New source: `P2GammaHeadWindowDictionary.lean`, intended module `ImbalancedChen.P2GammaHeadWindowDictionary`. Its only direct imports are `ImbalancedChen.P2GammaRetainedInteriorGeometry` and `ImbalancedChen.P2GammaSmallConductorIntervalBridge`, both frozen source-only suppliers requiring installation before this module. REGISTRY pins final source bytes and every declaration location.

For the original five cutoff values a,b,c,e,f, the head's effective `[L,U)` endpoints are:

| Colour | L | U |
| --- | --- | --- |
| 0 | a | min(f,b) |
| 1 | max(a,b) | min(f,c) |
| 2 | max(a,b,c) | min(f,e) |
| 3 | max(a,b,c,e) | f |

All earlier failed tests are kept. No ordering hypothesis on the real cutoff values is needed. `mem_headCarrier_iff` binds these endpoints to O's exact `headCarrier`, and actual membership supplies `c <= 3`. Colours above 3 have empty original carriers.

`source N t colour M` is the actual original head intersected with `M < p <= 2M`. Its exact SW endpoints are

```
u = max M (ceil(L) - 1)
v = min (2M) (ceil(U) - 1).
```

The subtraction is in the reals after the natural ceiling. This retains primes equal to an included left endpoint and excludes primes equal to the original strict upper endpoint. It does not round an original `[L,U)` to `(L,U]`.

`source_nonempty_geometry` uses an actual occupied prime to derive `M <= u <= v <= 2M`; it does not assume all grid cells are occupied. `source_eq_prime_filter` proves that the row equals `primeSWInterval u v` filtered by primality and coprimality to the same N. `source_weighted_sum_eq_interval`, `source_rowTransform_eq_interval` and `source_smallConductorContribution_eq_interval` transfer the literal row exactly to `targetDeleted N (profilePrimeCoefficient f)`. The independent k gate, primitive conductor, phi(r*k) denominator and r*k<=Q carrier are unchanged.

The short ceil arithmetic helper was private in the existing `P5OriginalSingletonPrimeSource.lean`; its body is materialized here because its Lean name is inaccessible across modules. The old/new proof bodies are statically byte-identical after stripping surrounding whitespace, with SHA256 `822a06b5805cfd261ede0b9dd775b260754766fc1544491ab7e4139702613fd0`. This is necessary reuse, not a new arithmetic proof or a second natural/integer bridge.

`source_subset_Icc` and `prime_interval_subset_Icc` supply the concrete positive cap `floor(2M)`. `source_lowConductorTotal_eq_interval` calls O's existing `lowConductorTotal_eq_smallConductorContribution` on the two natural rows, rather than reproving integer casts. The arbitrary complementary row remains unchanged and needs its original positive support bound.

## Actual hats, original retained source and small conductors

`head_grid_weighted_sum_eq_source` and `head_grid_rowTransform_eq_source` use O's existing nonzero hat support and factor-two comparison at `M = lower delta j`. They remove the extra dyadic cut exactly when `0 < delta` and `2 delta <= log 2`. Thus the dictionary applies to the whole original head hat, not merely an unrelated clipped subrow. `head_grid_weighted_sum_eq_interval` leaves the test F arbitrary, after the fixed row; the corresponding character transform equality keeps its k projector.

`retained_cartesian_head_row_eq_interval` leaves P's `rootComplementLabels` and `betaLabel` verbatim. `original_retained_row_eq_prime_interval` directly invokes P's already proved `original_retained_row_eq_cartesian`, then the head dictionary. It has no assumed source identity. The old marked pair, every remaining specified prime and colour, all complement masks and multiplicities, and the exact quotient including 1 remain inside the same beta. The complete product in F remains `product (t.1*t.2) y * p`.

`original_retained_row_eq_zero_of_empty` covers an empty clipped head row using the same original identity. No original source term is silently dropped.

`actual_head_small_conductors` directly calls existing O `variable_profile_small_conductors`. `actual_head_grid_small_conductors` then supplies the actual hat's differentiability/integrability from O's smoothness, and its variation from existing `exists_complexWeight_Abel_budget`. It explicitly branches on an empty source: the literal head transform is zero and no reversed endpoint is passed to SW. The final theorem does not require every chart to be nonempty.

The fixed geometric orders eta,J,W,Ctarget precede D,C,x0. Every varying x, delta, grid index, original N, marked pair, colour, conductor/quotient cutoff and complementary coefficient follows those constants. The remaining scalar norm condition is exactly `1 + 2D/delta <= W(log x)^J`; this is not an SW/BV estimate inserted as an assumption. The complete local-scale and target-size requirements remain the existing prime supplier's requirements.

## Exact closure boundary

The omitted finite deduction/API obligation `literal_colour_interval_attachment` is supplied at source level, including original retained-row attachment, empty rows and the actual small-conductor call. No P grid, Abel estimate, retained/rejected identity or natural/integer bridge was reconstructed. Existing source remains uncompiled and carries no kernel credit.

Remaining for the full Gamma argument: actual complementary L1/L2 norms and caps, all source-scale/gap inputs, ordering and upper-product rejected-mass payment, enlarged lower-residual assembly, complete conductor/chart/mother sums and the final original-N threshold. This packet neither assumes nor proves a complete BV or same-rho PP statement. Category (1) is untested Lean elaboration; category (2) is this supplied finite endpoint deduction. No new category-(3) manuscript gap is asserted by this task; P's quantitative rejected-strip issue is outside this endpoint conversion.

Static work only: exact text/import/declaration inspection, raw hashing, fixed-ref source reads, proof-body comparison, JSON parsing and forbidden-escape scan. No axiom, sorry, admit, unsafe, evaluator, compiler, numerical replay or Git operation was introduced or run. Finite guards in dependencies remain UNEVALUATED.
