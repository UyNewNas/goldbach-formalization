# Q18 — actual retained Gamma norms and complete scales

Status: **SOURCE-WRITTEN, UNCOMPILED, ZERO FORMAL CREDIT.** The actual retained-row L1/L2/cap and complete-scale obligations are supplied by three new source candidates. The full Gamma / same-rho PP node remains **OPEN**. No compiler, Lean/lake, CI, proof guard, numerical replay, Git operation, old-source modification or child agent was used. All dependency guards remain UNEVALUATED.

## Original requirement and difficulty classification

The inspected manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Lines 258–278 require original labelled prime weights, fixed logarithmic derivative costs, no new arithmetic filter, and the same rho in count and exact q-coprime mean. Lines 316–341 require the **complete** local product scale and retained smooth charts before the low-rank below-half BV call. The completed local note `../chen-imbalanced-semiprimes/proof-library/source/low-rank-convolution-bv-20261010.txt` (SHA256 `88edfb5f605e65ad7f05a702a963b5dff1b21f0b4e757edbf4eaed304f4e8f56`) specifies the two original square norms at 10–13, fixed divisor exponents at 28, and original-factor, complete-scale, q-independence and post-loss requirements at 132–148.

Q BRIEF, P conductor/geometry REPORT and REGISTRY, P t27 independent review, Q02 reuse inventory, and the actual source bodies were read before implementation. Production, prior source-only batches and hidden `.lake/proof-continuation/source-reviews/drafts` were searched. No already-written retained-row norm/cap transport was found. Existing geometry, first/second divisor moments, primitive LS, conductor sums and scale transport are reused, not reproved.

The norm/cap transport and actual complete-scale instance are category **(2)**, omitted finite deductions from named suppliers. Lean elaboration and API compatibility remain category **(1)** and were not tested. The absence of a paid sharp ordering/upper residual is a separate possible category **(3)** source issue identified by P; this packet neither proves such a gap impossible nor assumes it away. Q16/Q17 own residual payments, and no residual theorem is duplicated here.

## Actual rows and exact source connection

`P2GammaRetainedActualNorms.lean` keeps P's literal `betaLabel`. Its `retainedBeta` is

```
rootComplementCoefficient N t (c::cs) (betaLabel N t H delta j l).
```

`retainedComplementSupport` is the image of the original projected labels with nonzero beta weight. A product image only enumerates the support: `retainedBeta` still **sums the complete product fibre**, preserving every distinct original tail/quotient label. The old marked pair, remaining word, original roughness and target masks, and quotient 1 remain unchanged. No number of possible head primes is charged.

`retained_complement_test_eq_grouped` proves the exact labelled-to-coefficient sum for any later test F. `retainedBeta_zero_off_support` proves the required zero extension. `retainedComplementSupport_window` and `_subset_cap` derive

```
B < m < upper(delta,l) <= 2B,    B = lower(delta,l),
T subset Icc 1 (floor(2B)).
```

The prime coefficient is exactly `targetDeleted N (profilePrimeCoefficient (complexWeight delta j))`. Its finite carrier is Q15's actually implemented clipped colour interval. Q15 was consumed only after its source existed and was frozen at SHA256 `a462044e4af8fd4125f94be0ebcb756e073a35615e2e3598e31b4b618d729617`.

`P2GammaRetainedPhysicalRows.original_retained_row_eq_actual_rows` combines Q15's `original_retained_row_eq_prime_interval` with the new complementary fibre reindex. The result is an exact natural rectangle for the literal P retained row, for arbitrary later F. This preserves the exact q-coprime mean by taking the same arithmetic kernel on both sides; it does not insert an arbitrary coupled smooth amplitude into a supposedly separated row. `occupied_head_geometry` derives the valid colour and nonempty interval from a nonzero physical term. Nonoccupied original retained rows are proved zero for every F.

All row/support definitions have only N, the marked pair, the fixed original word, H, delta and grid indices as arguments. They have **no q, conductor, character, auxiliary quotient k, or moving-residue argument**.

## Raw norms, padding and quotient masks

For the original word of length `E=(c::cs).length`, put `D=(E+1)^2-1`. These exponents depend on the fixed original word and never on the requested accuracy, target or auxiliary quotient. At `M=lower(delta,j)`, `B=lower(delta,l)`:

| Actual quantity | Supplied bound | Source of proof |
|---|---|---|
| Prime coefficient supremum | 1 | Actual hat bound, prime indicator, target deletion |
| Prime L1 and square sum | `2M` | Positive interval support, finite cardinality, supremum bound |
| Complement L1 | `2B*(1+log(2B))^E` | P actual divisor domination + native `sum_fouvryTau_le_real` |
| Complement square sum | `2B*(1+log(2B))^D` | M `actual_mother_complement_square_sum` on the actual new support |
| Prime/complement padded caps | `floor(2M)`, `floor(2B)` | Actual interval/hat support, including arbitrary short intervals |

`paddedRow_energy` reuses O's already-proved complex integer/natural reindex, then takes its real part. It gives an equality of padded energy and the actual finite natural square sum. It does not reproduce the character bridge or generic large sieve.

The independent natural k-unit mask contracts L1. The existing `unitMask_energy_le` contracts both padded energies. No k-dependent factor is introduced and the existing prime small-conductor supplier retains its original fixed `C0=1`; this packet does not strengthen or replace that supplier.

At `x=M*B`, `log x>=1`, `M,B>=1`, the actual normalized data are

```
Ea <= 2^2 M (log x)^D,
Eb <= (2*3^D)^2 B (log x)^D,
mass(beta) <= (2*3^E) B (log x)^E,
P <= 2^2 M,             V <= 2^2 B.
```

Thus P's existing local consumer takes `eta=34/1135`, `ea=2`, `eb=2*3^D`, `c=2`, `em=2*3^E`, `C=D`, `Hmass=E`. The original two energies are **proved outputs**, not premises. P's `primitive_scale_bounds` already converts these caps and positive factor scales to its combined length/energy inequalities; that proof is not rewritten here.

## Complete physical scales and quantifier order

For any occupied retained chart, `occupied_scale_geometry` proves

```
H <= M*B <= N,
N^(68/1135) <= 2M,
N^(417/2500) <= 2B.
```

The first relation comes from the explicit P retention endpoints. The factor floors come from O's actual `original_two_factor_floors`, after proving that the nonzero retained head/complement pair is an original legal label. The second floor comes from the **old marked pair inside the complete complement**, not from the residual quotient and not from an invented positive-length unit sequence.

`exists_occupied_power_threshold` reuses P's existing fixed-constant power absorption at `eta=34/1135`. One original-N threshold precedes every marked pair, word, delta and pair of grid indices and yields `x^eta<=M,B` for every occupied row.

For the actual plateau-compatible choice `H=2*N^(1-kappa)`, `occupied_trim_complete_scale` supplies

```
N^(1-kappa) <= x <= N,     N <= x^(1/(1-kappa)).
```

The last inequality supplies `Ctarget=1/(1-kappa)` to direct target deletion. `exists_trim_occupied_scale_threshold` instantiates P's existing original/local common-threshold theorem at `x0=exp 1`; the same original-N threshold also gives `log x>=1` and `M,B>=1`.

Finally, `exists_physical_rows_norm_threshold` places the **actual** clipped alpha and retained beta into every displayed norm/cap/scale bound at one threshold. It does not leave `hM`, `hB`, `hlog`, any norm estimate, `energyProduct`, or a source identity as caller premises. Its physical selection premise is a nonzero actual retained term; the separate exact zero theorem handles all remaining rows.

## Reuse and remaining boundary

The REGISTRY pins all new sources, direct-import resolutions, declaration lines, inspected source paragraphs and selected native APIs. Principal reused suppliers are:

- M `P2OriginalGammaDivisorNorm`: actual fibre coefficient, fixed divisor norm and actual mother second moment.
- O `P2GammaOriginalCartesianMask`, `P2GammaSmoothLogGrid`, `P2GammaSmallConductorIntervalBridge`, and `P2GammaConvolutionLargeConductor`: original factor floors, hats, padding reindex and k-mask energy contraction.
- P `P2GammaRetainedInteriorGeometry`, `P2GammaOriginalScaleTransport`, and the existing primitive/local-conductor consumers.
- Q15 `P2GammaHeadWindowDictionary`: exact original colour/half-open interval and head-source attachment.
- Native `LiLiuPrereqFouvryDivisorMean.sum_fouvryTau_le_real`: the existing first divisor moment. No new moment theorem is claimed.

The full local BV application still requires the actual profile budget `1+2Dhat/delta <= W*(log x)^J` for the chosen grid, the post-loss below-half modulus gap, and the relevant common conductor threshold. Final chart/mother occurrence summation, the signed same-rho attachment, all residual payments, arbitrary permitted additional smooth/Fourier amplitudes and the general singleton-prime PP branch are outside this packet. Q16/Q17 work is not imported or credited here. A finite mother-family maximum of the existing local thresholds is still part of that assembly; no evaluated numerical word count is asserted.

Q27 independently read all three final mathematical source bodies and gave a **bounded static source PASS**, preserving these remaining HOLDs. Raw hashes, import/declaration locations, JSON and forbidden-token scans are static checks only. They do not certify installed imports, successful elaboration, transitive axiom freedom or kernel acceptance. No new source was installed into production.
