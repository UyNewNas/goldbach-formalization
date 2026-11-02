# P / medium_spectral_dictionary

Status: **PARTIAL SOURCE SUPPLIER; full original spectral dictionary and P3.5.uniform_spectral OPEN**. Task 18/30, `/root/t18_spectral_dictionary`. All three new Lean files are source-only: `compiled=false`, `kernel_verified=false`, `formal_credit=0`, finite guards **UNEVALUATED**. No Lean, lake, compiler, CI, finite guard evaluation, numerical replay, Git operation, production edit, old-batch edit or child agent was used. Only this assigned P directory was written.

The new work supplies actual original primary coefficient rows and their exact arithmetic/physical scalar association. It does **not** supply the requested full nonempty automorphic `PacketData`, a Kuznetsov identity, an ABL estimate, Eq24, or the 7/32 return. No desired dictionary equality or energy inequality is a hypothesis.

## Read-first and deduplication

`BRIEF.md`, this task's `PRIOR_TASK.json`, both complete O source files, the M prefix/outer reports, the N independent prefix/outer review, the M/K exceptional-kernel sources and reports, and the actual production `PacketData` definitions were inspected. The O directory contains exactly the two Lean files listed below and **no O REPORT.md or REGISTRY.json** at inspection. They were retained as imports and not repaired or copied.

Production already contains the finite primary/sign/y-dyadic partition and the exact normalized-F scalar calculation. Neither is reimplemented. Searches of production and preceding batches found no actual original `(level,n)` carrier construction that closes the gap: the only explicit new `nCarrier :=` construction found in the relevant M/K/O sources is M's empty-row prefix helper. Its intended purpose is interval indicator inversion, not the original spectral packet.

Exact principal reuse sources (all paths are relative to the repository root; raw hashes are also recorded with declaration lines in REGISTRY):

| Source | Reused declarations / reason | SHA256 |
| --- | --- | --- |
| `docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCompletedReciprocalSource.lean` | `OriginalData`, `originalSource`, `original_output_licensed`, `original_output_bounds`, positive six-smoothing and signed source identities | `cc3785b59a379b1d39d79a09be87cb7d3b46acf9ee4510ebe0149feb9786d1b5` |
| `docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCommonPoissonLanes.lean` | `commonMBlock`, `commonMBlock_normalized`, `jointMass_eq_resolved`, actual zero/block/tail kernels | `1c15c03a6fa6a1c188e8f5f2498aaee5f14da01b05e48676b263f9f3df1919e4` |
| `docs/source-only/20261102-resume-30m/medium_prefix_completion/Part3OriginalSimultaneousPrefixCompletion.lean` | Completed original lambda, one rough-s frequency outside the entire outer energy | `6ae388d0d329ec44592641755e7486079e66e8c3976cbfa8392632cae6e25039` |
| `docs/source-only/20261102-resume-30m/medium_outer_energy/Part3OriginalMaskedOuterCaller.lean` | Original positive outer/divisor normalization, kept upstream | `5da80a67265695179f59d1be33b8ba131c230101a447fd016e5c3d326f95851d` |
| `ImbalancedChen/Part3ActualReciprocalSquarePoisson.lean` | `completedPiece`, `sixSmoothMass_eq_completed`, literal signed Poisson summands | `4dd4d1487658283645a8c7857864df5448deb665828ac7c4a6cade294872b60e` |
| `ImbalancedChen/Part3ActualCompletedSquarePushforward.lean` | `weighted_pushforward`, `completedPiece_eq_source`, literal joint output and coefficient | `17dd930a8ed88c4f4e35c5a4eacc7d61aa77972a5742963942f1751b3c13a1ef` |
| `ImbalancedChen/Part3FixedRhoPrimarySignedFiniteDecomposition.lean` | Computed primary multiplier and signed exact quotient; prime support and coprime quotient | `7a9c64b902f314265eb61c737d6fc419309ebac59f669e7f96f817d5beb58095` |
| `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean` | `finite_source_assembly`, `beta_block`, `signed_beta_block_eq`, `assembled_beta_coprime` | `20fd20a906072b054fdfd65ba8cada3c1f8504a73d15b2455040dec0f346f935` |
| `ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean` | `signedY_div`, `dyadicPacket`; existing `nonempty_endpoint_bounds` remains the actual length >= 1/2 supplier | `8d8f41a161cf423e3944863cdf7ae8304c1536315a72b198cd6ae4eab8b6dd10` |
| `ImbalancedChen/Part3ActualCuspScalingSourceOnly.lean` | The two exact opposite cusp-phase product identities only | `871df77d2c8a87ca66dbb03341b91beb778a5eb338206d779e931785b93fe52d` |
| `ImbalancedChen/Part3ActualPoissonNormalizedFScalar.lean` | `poisson_scalar_match`, `chart_eq_spectral_point`; no discrete-c Jacobian | `dff1946c0f2498d1be0bf692aac58860841ba43699413e40d819578b778bc3d4` |

The complete source and imported-declaration inventory is in REGISTRY. Import paths for the O and new P modules are proposed installation modules; they are not silently claimed to exist in production. Held dependency closure and independent kernel acceptance remain unverified.

## New actual obligations removed

1. `Part3OriginalPrimaryPacketRows.lean` constructs the finite original `primaryBlock`, its joint `outputCarrier`, exact `levelCarrier`, level `outputFibre`, and natural `nCarrier`. The block key is the **existing computed key** `(nu, yDyadicIndex, ySign)`. Thus the sign and multiplier are original functions of y, not selected witnesses or overlapping divisibility filters.

   `outputCarrier_data` derives `nu>0`, `z>0`, `(a,z)=1`, `y!=0`, `nu|y`, the coprimality of `|y/nu|` to `|a|`, and the actual dyadic y bounds from a source witness. `decode_quotient` proves the signed reconstruction `y = signedY(sign,nu*n)`. `sum_outputFibre_eq_n` proves injectivity on the real fibre before using `sum_image`; `sum_output_eq_rows` then proves the exact joint-output to `(z,n)` change. Original source multiplicity stays inside beta; it is neither removed nor paid again by a counting estimate.

   `rowPacket` is an actual `CoprimePacket` on the subtype of occupied original levels. Its beta is the existing `dyadicBeta` of the **same OriginalData, completed lambda and omega**. `rowPacket_beta`, `rowCoefficient_eq`, `rowCoefficient_unphase`, and `norm_rowCoefficient` bind it exactly to the original block beta. The inverse cusp phase is explicit. This scalar unphasing is not an ABL oldform identity.

   `nonzero_original_beta_has_row` proves that every nonzero original nonzero-y beta supplies an occupied actual block, a real row, an n in its actual carrier, and a nonzero signed coefficient. This is the correct nonemptiness statement: the original carrier can be empty or all original coefficients can vanish, so an unconditional nonzero packet claim would be false. `levelCarrier_has_n` separately rules out padded occupied levels with empty n fibres.

2. `Part3OriginalPoissonPrimaryRows.lean` attaches those coordinates to the original completed source. `completedPiece_eq_zero_and_primary_rows` starts with production's `completedPiece_eq_source`, splits zero/nonzero y, invokes the existing exact primary partition, and performs the proved row reindexing. It has no supplied source identity.

   `original_six_eq_primary_rows` gives the six-piece equality with one global `J`, retaining:

   - the complete `y=0` term with **all** m;
   - for each nonzero-y primary/sign/dyadic block, its separate `m=0` row term;
   - the same positive and reflected-negative `commonMBlock J j` at every level, with the original signed frequency still in the kernel;
   - the explicit O summable outside-window tail.

   This is an exact complex equality. It does not pay the zero terms or the tail, and it makes no positivity assertion about an expanded individual term. The rough-s frequency `r` only occurs in the frozen original coefficient; it is never renamed Poisson m. No common Fourier additive phase is asserted to arise merely from selecting a common interval.

3. `Part3OriginalRowPhysicalScalar.lean` removes normalized-coordinate hypotheses from the existing scalar theorem's **original row-level** call. The true level bounds are `[S^2,4*S^2]`, which are too wide for the actual cutoff's `[1,2]` plateau. `levelChart` uses exactly `Z=S^2` below `2*S^2` and `Z=2*S^2` at/above that boundary; `levelCarrier_normalized` proves the requisite plateau condition. `nCarrier_normalized` supplies the y coordinate and O's actual `commonMBlock_normalized` supplies the positive m coordinate.

   `original_row_frequency_physical` then identifies the actual weighted signed Poisson summand with normalizedF at the physical argument

       q = 4*pi*sqrt(|a|*p*(nu*n))/(c*sqrt(z)),
       Y0 = 4*pi*sqrt(|a|*V*U)/(N*sqrt(Z)),
       rho = V*M/N.

   Both signs of m preserve their original Fourier argument and original Kloosterman indices. The scalar outside normalizedF is exactly `M*sqrt(Z)/(c*sqrt(z))`. The original modulus c remains discrete and is still governed by O's original c-unit filter. No continuous modulus substitution or Jacobian is introduced. This theorem works for the six original positive b/c scales and has only the explicit primitive `a!=0` and positivity/carrier premises.

## Ceil cutoff coordination: exact reuse, no duplicate proof

Task 19 supplied `docs/source-only/20261102-resume-30p/exceptional_j_eta/Part3OriginalAdditionalSpectralCosts.lean`, SHA256 `b616ee9bdef863d24216c36657b6269c93f2408da2babb03e59ed002a9fab5d2`. Its full cutoff proof was read. No copy or independent duplicate is added here.

- `commonMBlock_scale_le_twice_cutoff` (line 51) proves `V <= 2*x^epsilon*C/B` for a **nonempty actual** O block, including the ceiling.
- `exists_globalCutoff_six_rho_threshold` (line 111) chooses X before every OriginalData, x, j, M and N, uses the same `eta/2` original cutoff, and proves `V*M/N <= x^eta` for all six scales through `M<=2B`, `C<=N`. Its threshold pays both factors two using `4<=x^(eta/2)`.

This supports the literal rho in the new physical scalar identity. It is not imported as an estimate for a spectral packet and does not make the omitted-frequency tail small. It remains an uncompiled peer source with no inherited acceptance credit.

## Precise remaining boundary and difficulty classification

The original manuscript was read first at lines 201–254. Lines 207–210 require the retained phase charge and a common completed-variable interval/phase; lines 238–254 name normalized Kuznetsov, regular and continuous quadratic forms, coprime ABL, Kim–Sarnak and exceptional A/J, with coefficient `1_(n,a)=1 beta(nu*n,z)e(-n/z)`. The detailed source module was read at lines 299–367, particularly 323–333 and 349–367. Its raw hash is recorded below.

The new quotient reindex and actual scalar caller are difficulty **(2), fillable omitted deductions**, now supplied as complete proof bodies. The cross-file open-namespace issue found during independent static inspection was difficulty **(1), Lean expression/API** and was repaired in the new P file; no O or production file was changed.

The remaining full arithmetic-to-spectrum association is difficulty **(3), substantive source-interface gap**, not merely a missing namespace. This is not a proof that the manuscript is false. Precise evidence is:

- `ImbalancedChen/Part3ActualLiteralPacketIntegral.lean:210` defines `PacketData` with chosen rows, packets, n carriers, positive scales, normalization boxes and a continuous kernel. Its literal `physical`/`modeCore` Fourier reconstruction is a theorem about that chosen object; it does not provide a constructor from O's original Kloosterman source.
- `ImbalancedChen/Part3ActualCommonHeightKFactorizationFullGram.lean:47` defines `completedPacketSum` using only a common m weight and the signed transformed beta. It has **no actual automorphic Fourier coefficients** `R_{j,infinity}(m)` and `R_{j,1}(n)`. The exact factorization at line 103 explicitly makes this absence visible. This coefficient sum cannot simply be identified with the automorphic packet required by the stated large sieves.
- K's `Part3ActualExceptionalJPacketAdapter.lean:64` replaces `P.kernel` by the single normalized positive J/q function. Its physical equality is sound for that replacement, but inserting a kernel containing genuine automorphic Fourier factors and then applying this replacement would remove those factors. The existing scalar transform estimate is not the required normalized Kuznetsov association.
- Production's `signed_cusp_phase_cancel` in `Part3ActualPoissonNormalizedFScalar.lean` proves scalar exponent cancellation only. It does not prove the coprime oldform ABL identity with dilation-dependent Hecke factors and its cost.

Still required, with no target-shaped hypotheses substituted:

1. Complete the sum-level assembly by the two fixed Z charts, together with the physical normalized-F Fourier expansion, so the common m interval and physical phase are associated with the original whole row family. The present binary `levelChart` and row-level scalar identity are not that whole-family assembly.
2. Prove the source-bound normalized Kuznetsov/cusp identity for the original signed Kloosterman sum, including the exact cusp modulus, `1/(c*sqrt(z))`, test normalization, actual Fourier coefficients, regular/exceptional branches and the continuous quadratic form.
3. Prove the actual coprime ABL/oldform extraction and height independence of the resulting coefficients. The constructed scalar coefficient rows are necessary arithmetic data, not an estimate for the actual spectrum.
4. Apply the genuine spectral inequalities with the required **length at least 1/2**, using the existing `nonempty_endpoint_bounds` after `rowPacket_beta` on nonzero coefficient rows. A generic PacketData `(-32,32)` box or an `U/nu>=1/32` assertion is not substituted for this endpoint. The common m dyadic length is also occupied-source data.
5. Pay the original zero-difference, m=0 and Poisson tail terms and assemble them with the actual original return; the new exact equations retain all three. No 7/32 estimate, Eq24 or D0/D1/D2 return is closed here.
6. Review the held dependency closure, stage the intended modules, and perform user-owned Lean elaboration and kernel verification later.

## Static checks and provenance limits

Manuscript: `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.

Detailed original module: `../chen-imbalanced-semiprimes/paper/source/modules/distribution-medium-completion-20261010.txt`, SHA256 `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`.

Static source scans found no admissions, axioms, unsafe declarations, evaluation directives, or finite numerical guards in the new Lean files. Declaration/import enumeration, JSON parsing, file existence and raw SHA256 checks are metadata checks only. No theorem was executed, elaborated or kernel checked. Local mathlib API text was inspected where used; checkout/import closure and package state remain unverified. The independent review is owned by task 29 and does not follow from this author's report.

Proposed install order: `Part3OriginalPrimaryPacketRows`, followed by `Part3OriginalPoissonPrimaryRows` and `Part3OriginalRowPhysicalScalar`, under their matching `ImbalancedChen` module paths after the frozen O/M dependency chain is staged. All broad nodes remain OPEN.
