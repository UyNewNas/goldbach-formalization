# Q19 / automorphic_dictionary

Status: **PARTIAL SOURCE SUPPLIER; original two-Z finite-source Fourier assembly supplied; normalized automorphic dictionary and P3.5.uniform_spectral OPEN**. Both new Lean files are source-only: `compiled=false`, `kernel_verified=false`, `formal_credit=0`. No Lean/lake/compiler, CI, proof guard, numerical replay or Git command was run. No old file, production module or other task directory was changed. No child agent was spawned.

The result is an exact equality for the original six-piece source, with one convergent Fourier series and an explicit remainder containing the old full zero-y, nonzero-y m=0 and outside-window terms. It is not a bound for that remainder, not a Kuznetsov formula, and not a spectral energy estimate. No dictionary, Fourier separation, energy, summability or desired estimate is accepted as a premise.

## Read-first and hidden-source deduplication

Read Q and P `BRIEF.md`, P `medium_spectral_dictionary/REPORT.md` and `REGISTRY.json`, P `reviews/t29_review_spectrum.md`, all three P source files, and the original manuscript at lines 201–254 plus `distribution-medium-completion-20261010.txt:299–367` before writing. Q `q03_original_gap_triage/REPORT.md` items 6–8 were subsequently read and reused for the boundary classification. The exact manuscript hashes remain:

- `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`: `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.
- `../chen-imbalanced-semiprimes/paper/source/modules/distribution-medium-completion-20261010.txt`: `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`.

Searches explicitly included production, all `docs/source-only` batches, and `.lake/proof-continuation/source-reviews/drafts`, with `rg --hidden --no-ignore` and both `.lean` and `.lean.txt`. Before these Q files existed, `levelChart` and `original_row_frequency_physical` occurred only in P's scalar file. Searches for original/fixed-Z whole-family HasSum constructions found no existing supplier in the inspected source set. This is a bounded source search, not a universal nonexistence claim.

The native period-64 reconstruction already exists. Its hidden predecessor was opened at `.lake/proof-continuation/source-reviews/drafts/20261023-P3-period64-continuity-opaque-plain-function-stages-SOURCEONLY.lean.txt` (hash `980bea3e95d150a9ea52b890230a99022167b9ec40cb2f8c4704e253837996fa`); production's `actual_global_separation_hasSum` is reused directly, not recopied. Also opened the hidden full raw-height energy file and actual Gamma0 unbounded scalar measure source. The former explicitly uses Lebesgue dt and is not automorphic Plancherel; the latter retains the possible zero spectral sector and supplies neither a cusp Fourier trace identity nor Kuznetsov normalization. Neither fills the requested dictionary.

Principal exact reuse:

| Source | Used declarations / boundary | Raw SHA256 |
|---|---|---|
| P `Part3OriginalPrimaryPacketRows.lean` | Actual `BlockKey`, `levelCarrier`, `nCarrier`, `blockBeta`, `rowPacket`; `nCarrier_normalized`, `rowCoefficient_unphase` | `a3e1953d1a521d55aa62c5911c7b524a2dd61210417d891027ec28900f84e287` |
| P `Part3OriginalPoissonPrimaryRows.lean` | `rowPairing`, `resolvedRows`, `primaryRowPiece`, `completedPiece_eq_primaryRowPiece`, `original_six_eq_primary_rows` | `ed0158c7f7aa105674533d2705609086b4d0b7b5f7aaec80f61735858c90ed1d` |
| P `Part3OriginalRowPhysicalScalar.lean` | Existing `levelChart`, `levelCarrier_normalized`, `original_row_frequency_physical`; scalar proof is not repeated | `e173cc2ba74075708f805856b0bd8ff7af4e1e4a3f213d4a4e2047785961a8ec` |
| O `Part3OriginalCommonPoissonLanes.lean` | Original half-open `commonMBlock`, global J, `commonPoissonCompleted`, signed kernels and explicit summable tail | `1c15c03a6fa6a1c188e8f5f2498aaee5f14da01b05e48676b263f9f3df1919e4` |
| `ImbalancedChen/Part3NativePeriod64Reconstruction.lean` | `actual_global_separation_hasSum`, `actualCoeff`, `spectralTest`, actual all-t reconstruction | `724b2fd91c84aad404bad66a023d9c9151ffe21358c22a141e96bbf17b7c31bb` |
| `ImbalancedChen/Part3ActualLiteralPacketIntegral.lean` | Only `modePacket` and `signedCoefficient_modePacket`; no PacketData constructor or physical theorem is treated as automorphic | `500b7c1476c8afb777551807f1f737b17d785aeafec401c7b691fd46b0b9aa55` |

P paths in this table are under `docs/source-only/20261102-resume-30p/medium_spectral_dictionary/`; O paths are under the corresponding `20261102-resume-30o/medium_spectral_dictionary/`. The P three raw hashes were independently recomputed and agree with P REGISTRY. Full source paths, direct imports, declaration lines and read-only audit evidence are recorded in this Q REGISTRY. No old import was materialized or silently claimed to exist in production.

## New source supplier

### 1. Whole original family at two fixed Z values

`Part3OriginalTwoZSourceAssembly.lean` defines the two values `fixedZ D false = S²` and `fixedZ D true = 2*S²` before choosing any z, n, c, p or Fourier index. `chartLevels` filters the actual P level carrier at `2*S²`, using `<` below and `≤` above. `chartLevels_disjoint` and `sum_levelCarrier_two_charts` establish the disjoint exact partition, including empty carriers and the shared boundary. `levelChart_eq_fixedZ` connects P's per-level chart to these fixed values; its existing normalization proof yields the whole-chart `[1,2]` plateau.

`sourceChartBlock_eq_physical` is the missing finite-family application of P's scalar theorem. It sums over the literal original level/n carriers, positive c range `Ioc 0 (floor (10*D.cScale))`, the original `c.Coprime z` filter and the same `commonMBlock J j`. It preserves:

- both y signs in `decode k z n = (z, signedY k.2.2 (k.1*n))`;
- both original m signs in `signedY negativeM p` and the Fourier argument encoded by sigma;
- the original Kloosterman arguments `signedY negativeM p * inverseResidue c z` and `a * signedY k.2.2 (nu*n)`;
- beta's original source multiplicity and the discrete modulus c;
- the exact scalar `M*sqrt(Z)/(c*sqrt(z))` and physical coordinates

  `q = 4*pi*sqrt(|a|*p*(nu*n))/(c*sqrt(z))`,
  `Y0 = 4*pi*sqrt(|a|*V*U)/(N*sqrt(Z))`, `rho = V*M/N`.

`rowPairing_block_eq_two_chartPhysical` gives the entire original signed block as the sum of these two fixed-Z physical families. There is no Jacobian replacement of a discrete c sum and no added carrier nonemptiness assumption.

### 2. Derive the common m phase from actual Fourier reconstruction

`Part3OriginalTwoZFourierAssembly.lean` applies production's `actual_global_separation_hasSum` to each literal physical point and takes the finite sums over the actual z/n/c/p family. `chart_hasSum` has a single `actualCoeff(rho,sigma,ell)` outside that entire chart family. Adding both charts gives `original_block_hasSum` for the original `rowPairing ... blockKernel`.

Each mode has the exact form

`commonPoissonCompleted(J,j,ell₁).weight(p)`
`* modulatedBeta(D,r,k,upper,ell,z,n)`
`* [M*sqrt(Z)/(c*sqrt(z))]`
`* spectralTest(ell,Y0,q)`
`* sourceKloosterman(D,k,negativeM,z,n,c,p)`.

Here `commonPoissonCompleted_weight_eq_e` proves the actual reconstruction character is

`1_(p in commonMBlock J j) * e(ell₁*p/(64*2^j))`.

It has no level, original rough-s frequency r, y-key, c, n or height input. Both Z charts use the same p interval and phase. For a reflected negative original m, p is its positive magnitude; the original negative m remains literal in `sourceKloosterman` and the negative Fourier argument remains in sigma. No beta is conjugated.

The other character is exactly

`modulatedBeta = blockBeta(z, signedY sign (nu*n))`
`  * e(ell₂*(nu*n)/(64*U) + ell₃*z/(64*Z))`.

It has no future m, c or spectral-height argument. `norm_modulatedBeta` proves the original coefficient norm is unchanged. `modulatedBeta_eq_unphased_row` connects it to P's actual modulated `CoprimePacket` while retaining the explicit inverse cusp phase. This scalar compatibility is not an oldform identity and pays no ABL factor.

### 3. One series for the original six-piece source; no lost lanes

`nonzeroBlocks_hasSum` takes the finite sum over all original computed primary/sign/y-dyadic keys and all common dyadic m indices. `completedPiece_eq_remainder_and_fourier` connects that series to the actual production `completedPiece`.

The final theorem `original_six_eq_remainder_and_fourier` proves, at the same `J = globalCutoff D x epsilon`,

`(smoothSix D r : Complex) = sixRemainder D r J + tsum (sixMode D r J)`.

The single Fourier index ranges over `Fin 4 -> Int`. The six b/c scale pairs are exactly `(B,C)`, `(B,2C)`, `(B,4C)`, `(2B,C)`, `(2B,2C)`, `(2B,4C)`. This is an actual finite/HasSum assembly, not an equality assumed for a chosen packet. The earlier r and later Poisson m have never been identified.

`pieceRemainder` is independently defined from the existing objects:

1. `jointMass ... (zeroSource (originalSource D))`, retaining **all** m when y=0;
2. `rowPairing ... zeroMKernel` for every original nonzero-y primary block;
3. `rowPairing ... tailKernel J` for those same blocks, retaining O's original outside-window summable series.

Thus zero-y and m=0 are not double-counted; the tail is not a subtraction-defined error. No size estimate for any of the three is provided by this exact identity. The final theorem uses only OriginalData, its original r, x/epsilon, a reconstruction order L, and `D.block.atom.residue ≠ 0`; the six positive scale facts are derived. No positivity, large-X cutoff, rho budget or support witness is accepted in place of a source theorem. Such inequalities remain separate from this exact equality.

## Narrow remaining boundary

The new deduction is difficulty **(2)**, an omitted finite/Fourier assembly, as in Q triage item 6 and manuscript `Medium:349–358`. The broad automorphic task remains OPEN. The remaining obligations must be separated:

1. **Modulus/test compatibility at the trace call (class 2).** The proved modes deliberately retain the original finite c range. After Fourier separation, the individual `spectralTest = chi(q/Y0)*e(...)` has a wider support than the original `scaledDyadicCutoff N c`; one may not simply drop the finite c cutoff separately in every mode and cite a full-modulus Kuznetsov formula. A future caller must first prove a common enlargement/zero-extension and the associated exchange, or another exact admissible test association. This candidate does not assert that its finite c mode is already a standard full-modulus trace-formula input. The normalized coordinate identity and compact support give a concrete route; the original discrete sum is never replaced by a continuous c integral.

2. **Source-bound normalized Kuznetsov (class 3 formal source interface).** Existing J `Part3OriginalNonzeroCuspOneSource.lean:298–314` already proves the arithmetic matrix conversion with the exact reversed phase `e(-a*y/z)`, and lines 345–366 apply it to its literal nonzero kernel. That is exact reuse, not a new missing scalar lemma. What is absent at the new original source is the normalized trace identity with actual Gamma0(z) Fourier coefficients, cusps infinity/1, the stated scaling matrices, positive cusp modulus `sqrt(z)*c`, test normalization and all regular/exceptional/holomorphic branches.

3. **Actual ABL/oldform association and full continuous form (class 3).** The actual Fourier product must contain `conj R_(j,infinity)(m) * R_(j,1)(signed n)` with the correct test and oldform labels. Coprime extraction must establish the original height-independent `1_(n,a)=1 beta(nu*n,z)e(-n/z)` at every dilation and its Maass squared cost `(|a|*nu)^(7/32)`; holomorphic and continuous branches have the stated theta=0 treatment. Scalar phase cancellation does not prove this. The arithmetic K=1 and actual classical endpoint work is coordinated with Q20, not duplicated here.

4. **Full genuine spectral energy and all remaining payments.** `ImbalancedChen/Part3ActualCommonHeightKFactorizationFullGram.lean:47–50` defines `completedPacketSum` without any automorphic Fourier coefficient. Its factorization at lines 103–115 makes this explicit. K `Part3ActualExceptionalJPacketAdapter.lean:64–68` replaces every kernel by a common J/q kernel, so it cannot preserve a genuine Fourier product inserted into that field. Neither is identified with this new signed Kloosterman source. K `Part3OriginalContinuousPacketExhaustion.lean:231–272` contains the correct product and full cusp measure for supplied raw rho functions, but its caller still requires automorphic realization and actual local/cumulative estimates. Hidden raw-height Fourier Plancherel and Gamma0 scalar measures are not substitutes.

5. **Original zero-y/m=0/tail estimates and final return.** The exact remainder remains to be paid at the same source carriers and six scales. P's existing ceil/six-rho/log/nu/D work is not repeated and does not itself estimate this remainder. Kim–Sarnak, the genuine A/J and regular cumulative calls, full continuous cusp sum, all endpoint/multiplicity costs and Eq. (24)/(25)/D0/D1/D2 returns remain unproved by Q19.

These are limits of the current formal source construction, not a counterexample to the manuscript. In particular, the new result does not infer automorphic closure from an arbitrary PacketData, replace a product by `positiveSignKernel`, or add an `hEnergy` consumer.

## Files, staging and validation limits

| New file | Intended installation module | Raw SHA256 |
|---|---|---|
| `Part3OriginalTwoZSourceAssembly.lean` | `ImbalancedChen.Part3OriginalTwoZSourceAssembly` | `5ab4eddbbe4cdfac80d517a1558565e07c1a9bd819c02e8b0e0ae5af30a063cc` |
| `Part3OriginalTwoZFourierAssembly.lean` | `ImbalancedChen.Part3OriginalTwoZFourierAssembly` | `f54ee12b12efd7a6de2c0323ae123f2e95d660bed8c44dba180a65af4001c990` |

Install only after the frozen O/M/P dependency chain has been staged; the proposed import names do not imply current production availability. Existing dependency proof bodies are not assigned new verification credit.

Performed only source reads, line/import/declaration enumeration, raw SHA256 comparisons, JSON parsing and scans for admissions/axioms/unsafe/evaluation directives. Those scans found no matches in the two new Lean files. Q29 independently read the candidate source and reported no definite finite-sum/HasSum API or object-preservation blocker at the communicated hashes; its final report is separate. This is not elaboration, compilation, kernel acceptance, a recursive import-closure check, or finite proof-guard evaluation. All broad nodes remain OPEN.
