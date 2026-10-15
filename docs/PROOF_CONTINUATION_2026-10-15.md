# Mathematical proof continuation — 15 October 2026

This branch continues the mathematical proofs from Dot's integration commit
`3c51704ff4da3abc94cd06e39e62ee2a1bc4f6af`. It does not replace Dot's CI work
or change the authoritative automation control files. The manuscript remains
`ba6ec11d800eccc54406490631895e174de85766`; the target is still the full
Theorem 1.1 and Corollary 1.2 with the original `currentC` and `currentK`.

**Neither `hLower` nor `hUpper` is proved.** All results below are components.
The new leaves are not imported into `ImbalancedChen.lean`; a successful
existing root build would therefore not validate them.

## Core goal and remaining dependencies

| Core dependency | Proved components | Still required for the manuscript theorem |
| --- | --- | --- |
| Chen lower ledger | Actual ordinary means for the first six rows; actual ninth upper mean with coefficient eight | Stronger causal contributions, remaining rows, and the complete eleven-term ledger |
| Strong physical distribution | Exact complex CRT, Fourier, Poisson and transposed covariance identities; accepted residual estimates are listed individually below | The full nonzero-frequency bound on the original physical range, including all remaining gcd regions |
| Original signed first-exit policy | Full nonlinear kernel integral convergence and actual compact prime harmonic limits | Exact original signed coefficient dictionary, the same-policy arithmetic mean, and its counting error |
| Final theorem and constants | Existing conditional numerical transfer and individually checked certificate lemmas | Derive the original `hLower` and `hUpper` and connect every required enclosure to the unconditional main theorem |

In particular, the proved ordinary ninth coefficient `8` is larger than
the required `8452171/1250000`. No change of normalization removes this gap.
Module and declaration totals below measure checked components, not a
percentage of the main theorem completed.

## Current analytic frontier (source audit only)

The fixed external Fouvry C.2 theorem does not directly cover the entire
original medium range. For example, the exponent tuple
`(sigma,kappa,u,v,q1,q2,q3)=(1/1000,0,1/4,3/4,6/25,19/100,3/20)`
passes the four original strict geometric inequalities and has physical
level exponent `29/50`; the retained-frequency scale can be nonempty.
The current binary-factor global scalar envelopes also fail to produce
power savings on this exponent domain. These are source/API and exact
exponent checks, not a counterexample to the desired distribution bound.
A stronger estimate retaining all three original factor scales is still
needed for the remaining region.

The audit and its private-API correction are preserved in the verification
archive (`source-reviews/20261016-both-small-reciprocal-actual-parameter-audit.json`
and `source-reviews/20261016-both-small-canonical-private-api-correction-addendum.json`).
Generic private phase lemmas are not treated as callable public APIs, and
original admissibility is not replaced by unproved transposed admissibility.

## New mathematical results with executed checks

| Module | Mathematical content | Verification |
| --- | --- | --- |
| `CurrentChenUpsilon6KernelBuffer` | Integrability, positivity on the corrected product domain, and the actual logarithmic kernel integral limit as the product buffer tends to zero | Strict compilation; original-object stock kernel replay; complete 24-declaration types, inventory and transitive axiom audit |
| `CurrentChenPairLevelGeometry` | Actual pair multiplier, integer Rosser level, compact U5 profile, and restricted U6 profile | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon6OrdinarySieveKernel` | Identification with the canonical normalized continuous lower sieve factor, and the same buffer limit | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `CurrentChenPairRosser` | Finite lower Rosser estimate for the actual quotient source, with the true `phi(b*d)` main term, full AP/centre errors and physical support `b*d <= Q` | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `Part3CenteredFourier` | Exact centered additive Fourier identities at composite moduli, retaining actual prime labels, weights and the primitive centre | Strict compilation; original-object stock kernel replay; complete 28-declaration types, inventory and transitive axiom audit |
| `Certificates.PairedV2FullBuchstab` | The actual Buchstab gain bounds the certified fibre kernel with `K/80 = (K/4)*(1/20)` used once | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `CurrentChenPairHarmonicMean` | The actual fifth prime-pair selector, its strict ordered triangle, true reciprocal-totient weights and varying-profile harmonic integral limit | Strict compilation; original-object stock kernel replay; complete 25-declaration types, inventory and transitive axiom audit |
| `ActualSieveGapTailDecay` | Canonical continuous sieve gap positivity, monotonicity and quadratic tail decay, with the real source DDE supplied | Strict compilation; original-object stock kernel replay; complete 11-declaration types, inventory and transitive axiom audit |
| `ActualSieveGapTailBounds` | Exact reference value at three, the normalized `3/s^2` bound and the explicit logarithmic tail-envelope limit | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `Part3ComplexDispersion` | Actual complex-row Cauchy, centered norm-square and double-label identities, retaining the full moduli and primitive centre | Strict compilation; original-object stock kernel replay; complete 30-declaration types, inventory and transitive axiom audit |
| `CurrentChenPairMovingHarmonic` | The same integral at the genuine rounded integer row parameter, with the actual total phi-weight bound paying uniform perturbations | Strict compilation; original-object stock kernel replay; complete 10-declaration types, inventory and transitive axiom audit |
| `ActualThirdPrefixTailIntegralCore` | Canonical correction kernel, finite noncompact triple-integral bounds and tail convergence allowing the cap/selector to vary with the cutoff | Strict compilation; original-object stock kernel replay; complete 59-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon5FiniteMean` | Actual U5 counts above the same row-dependent Rosser density sum, with full ordinary BV and centre costs paid; a fixed `B` precedes arbitrary `epsilon` | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdIdealCap` | Literal eight-branch/pair-gated ideal cap: measurability and finite vanishing noncompact canonical tail | Strict compilation; original-object stock kernel replay; complete 23-declaration types, inventory and transitive axiom audit |
| `Part3ComplexCRTConsumer` | Actual complex W becomes a constructed lcm CRT progression, with incompatible/inactive labels and the primitive-centre V/U retained | Strict compilation; original-object stock kernel replay; complete 25-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdOrderedIntegral` | Actual clamped correction kernel: measurability, Fin-3 Tonelli to nested integration, integrability and real integral identification | Strict compilation; original-object stock kernel replay; complete 28-declaration types, inventory and transitive axiom audit |
| `CurrentChenRosserEndpointDictionary` | Exact actual initial-sieve product, nu=1/phi, Euler product and ceil-level dictionary; uniform genuine Mertens local bound | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `CurrentChenRosserLowerRectangle` | Uniform canonical AllDepth lower estimate on the actual initial sieve; rounding, sourceSigma and adaptive-depth error paid | Strict compilation; original-object stock kernel replay; complete 3-declaration types, inventory and transitive axiom audit |
| `CurrentChenFixedEulerNormalization` | Actual target-prime-deleted Euler product at fixed positive power cutoff has the genuine 2 exp(-gamma)/a normalized limit | Strict compilation; original-object stock kernel replay; complete 39-declaration types, inventory and transitive axiom audit |
| `CurrentChenPairDensity` | Uniform one-sided normalized density bound for every genuine rounded fifth-row level | Strict compilation; original-object stock kernel replay; complete 31-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon5OrdinaryMean` | Actual fifth-row ordinary count mean with the genuine moving harmonic integral and complete BV/centre payment | Strict compilation; original-object stock kernel replay; complete 10-declaration types, inventory and transitive axiom audit |
| `CurrentChenInitialRosserRemainder` | Actual initial count above the same Rosser density with complete ordinary BV and centre errors paid | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `CurrentChenOrdinaryInitialMean` | Actual initial ordinary mean at full Q+1 level for every fixed 0<a<1/4, using canonical f at the genuine ratio 1/(2a) | Strict compilation; original-object stock kernel replay; complete 32-declaration types, inventory and transitive axiom audit |
| `CurrentChenOrdinaryInitialLedger` | The first two actual current Upsilon rows receive their full ordinary means at the original current cutoffs | Strict compilation; original-object stock kernel replay; complete 2-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon6OrdinarySource` | Literal corrected inner sixth selector and actual quotient counts, with only nonnegative counts dropped and E=False scope retained | Strict compilation; original-object stock kernel replay; complete 13-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon6FiniteMean` | One BV exponent pays all errors for every actual sixth-row subselector chosen after N, retaining the full physical moduli and row coefficients | Strict compilation; original-object stock kernel replay; complete 20-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon6OrdinaryMean` | Actual unmasked sixth-row ordinary mean: fixed-buffer arithmetic limit followed by the proved buffer-removal integral limit | Strict compilation; original-object stock kernel replay; complete 61-declaration types, inventory and transitive axiom audit |
| `CurrentChenQuotientUpperRosser` | Actual quotient count upper Rosser bound with the complete physical-modulus AP and centre errors | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `CurrentChenSinglePrimeUpperFiniteMean` | One ordinary BV budget pays every actual third-row subselector and the genuine fourth-row finite upper count | Strict compilation; original-object stock kernel replay; complete 26-declaration types, inventory and transitive axiom audit |
| `CurrentChenRosserUpperEndpointDictionary` | Exact actual upper Rosser weight, reciprocal-totient coefficient, product and ceil-level dictionary | Strict compilation; original-object stock kernel replay; complete 2-declaration types, inventory and transitive axiom audit |
| `CurrentChenRosserUpperRectangle` | Uniform genuine canonical AllDepth upper factor for every s>1, with all actual level and adaptive-depth errors paid | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdClosedIntegral` | Actual affine diagonal null wall pays the closed ordered domain; old-cube equality is paid by the clamped lower factor | Strict compilation; original-object stock kernel replay; complete 20-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdPhysicalCell` | Literal closed ordered robust Gamma cells: retention/transition walls, two whole-cell pair gates, ideal domination and uniform small-z margin | Strict compilation; original-object stock kernel replay; complete 42-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdDyadicCoverage` | Actual dyadic ownership, unique retained coverage away from the displayed stopping strip and uniform fine-grid bounds | Strict compilation; original-object stock kernel replay; complete 23-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdLowerFactorRegularity` | The same canonical clamped lower factor is globally continuous, nonnegative and bounded by 1/(2 exp(gamma)) | Strict compilation; original-object stock kernel replay; complete 5-declaration types, inventory and transitive axiom audit |
| `Part3ComplexCRTFiniteFourier` | Same common finite source split into the actual mass/lcm zero mode and complete nonzero Fourier term, retaining V/U | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `Part3CommonSmoothCutoff` | One genuine smooth bump, Schwartz Fourier decay and its actual medium-atom common smooth Cauchy consumer | Strict compilation; original-object stock kernel replay; complete 46-declaration types, inventory and transitive axiom audit |
| `Part3CommonPoisson` | Actual common smooth progression to integer lattice, Schwartz Poisson and the full nonzero-frequency remainder, retaining the true complex labels and V/U | Strict compilation; original-object stock kernel replay; complete 31-declaration types, inventory and transitive axiom audit |
| `Part3FactorFiberDivisor` | Actual physical-modulus factor fibres retain all labels, with a proved tau_3 majorant and explicit logarithmic second-moment costs | Strict compilation; original-object stock kernel replay; complete 30-declaration types, inventory and transitive axiom audit |
| `Part3RealComponentReduction` | Exact 32 real-component expansion of the actual five complex coefficients; same family-uniform SW constants and explicit square cost | Strict compilation; original-object stock kernel replay; complete 37-declaration types, inventory and transitive axiom audit |
| `CurrentChenSinglePrimeUpperDensity` | Actual rounded single-prime upper Rosser density with canonical upper factor and fixed Euler normalization | Strict compilation; original-object stock kernel replay; complete 22-declaration types, inventory and transitive axiom audit |
| `CurrentChenTrueLiNormalization` | Genuine leading-one normalization of the actual logarithmic integral, proved without an asymptotic supplier premise | Strict compilation; original-object stock kernel replay; complete 14-declaration types, inventory and transitive axiom audit |
| `CurrentChenSinglePrimeHarmonicMean` | Actual single-prime reciprocal-totient sums with moving row profiles have their genuine harmonic integral limits | Strict compilation; original-object stock kernel replay; complete 23-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon34OrdinaryUpperMean` | Literal third- and fourth-row ordinary upper count means with their original cutoffs and complete error budgets | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdFirstCubeMargin` | Actual retained robust cap has the displayed positive first-cube margin | Strict compilation; original-object stock kernel replay; complete 6-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdGammaApproximation` | Literal robust Gamma approximates the same eight-branch ideal cap outside the explicitly paid transition and stopping strips | Strict compilation; original-object stock kernel replay; complete 20-declaration types, inventory and transitive axiom audit |
| `Part3CanonicalReciprocalData` | Canonical finite gcd-factor data constructed from actual compatible CRT row labels, including the true lcm reconstruction and phase-unit gates | Strict compilation; original-object stock kernel replay; complete 108-declaration types, inventory and transitive axiom audit |
| `Part3CanonicalReciprocalPhase` | Exact three-phase dictionary for the actual signed CRT residue and all integer Poisson frequencies, retaining the slow term, full complex labels and primitive V/U | Strict compilation; original-object stock kernel replay; complete 28-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9PrimeSource` | Literal ninth source is exactly a prime-triple part plus the actual unit fibres, proved from its genuine square-root rough cutoff | Strict compilation; original-object stock kernel replay; complete 25-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9UnitBudget` | Actual ninth unit fibres have a concrete 4 N^(92/125) bound and a proved negligible singular-normalized contribution | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9ProductCoefficient` | Literal ordered prime-pair products give a modulus-independent zero-one coefficient on the genuine power interval, retaining the original quotient and unit fibres | Strict compilation; original-object stock kernel replay; complete 30-declaration types, inventory and transitive axiom audit |
| `Part3CleanBetaLargeGCDMajorant` | Actual large-gcd W splits into a clean-beta divisor majorant and the complete explicit signed-divisor exception | Strict compilation; original-object stock kernel replay; complete 26-declaration types, inventory and transitive axiom audit |
| `Part3PolynomialResidueDivisorBound` | Genuine divisor subpower bound pays the actual moving polynomial residue in the original scale, retaining clean-pair mass and the exception | Strict compilation; original-object stock kernel replay; complete 14-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdFinitePhysicalKernel` | Literal finite retained-cell lookup, measurable actual clamped kernel, compact bound and uniform canonical nested small-z tail | Strict compilation; original-object stock kernel replay; complete 21-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdStripIntegral` | Actual transition/stopping strips have vanishing compact-kernel mass with the displayed uniform volume and threshold order | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdCompactKernelApproximation` | The actual finite kernel uniformly approximates the unbuffered ideal kernel off the exact two strips, paying both level changes and a genuine canonical modulus | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdFiniteTailIntegral` | Actual finite physical lookup has a genuine tuple-space Tonelli and closed-order tail bridge to the uniform canonical small-z bound | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdBoundaryLoss` | Full actual physical and ideal transition/stopping-strip masses vanish after paying the compact and uniform small-z parts in the displayed threshold order | Strict compilation; original-object stock kernel replay; complete 8-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdKernelL1Convergence` | Whole-domain absolute L1 error of the actual finite lookup against the unbuffered ideal kernel tends to zero with one cutoff before all buffers and meshes | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdFunctionalConvergence` | Full-domain integrability of the actual physical and ideal kernels, and uniform convergence of the finite-policy real integral to the literal unbuffered manuscript functional | Strict compilation; original-object stock kernel replay; complete 11-declaration types, inventory and transitive axiom audit |
| `Part3ActualLargeGCDBetaMass` | Actual clean complex beta norms have a proved large-gcd pair-mass bound at the original length, with explicit logarithmic cost and the original exception retained | Strict compilation; original-object stock kernel replay; complete 15-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9CoprimeGateBudget` | Actual signed upper Rosser coprimality defect of the same zero-one ninth coefficient has a proved N^(106/125) log(N)^2 budget and a negligible singular-normalized contribution | Strict compilation; original-object stock kernel replay; complete 15-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdLeastWinningIndex` | Deterministic least maximizing actual cell branch; real infimum and tie-priority arguments exclude failed-pair and unsupported p2 choices | Strict compilation; original-object stock kernel replay; complete 28-declaration types, inventory and transitive axiom audit |
| `ActualTwoCapacityGreedy` | Deterministic prefer-left allocation under the original-vector prefix-square condition, retaining natural products, labels, capacities and full-vector repair | Strict compilation; original-object stock kernel replay; complete 14-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdFiniteCellIntegral` | Exact finite decomposition of the actual nonlinear retained-cell kernel and its genuine integrable ordered cell integrals, with uniform convergence to the literal manuscript functional | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdActionParameters` | Actual selected branch parameters in the required interval, with the true rescue equality dispatch and pair gate/endpoint margins | Strict compilation; original-object stock kernel replay; complete 16-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9PanAggregate` | The actual modulus-independent zero-one ninth coefficient receives a proved bounded Pan aggregate and exact coprime-defect decomposition, with one fixed B before all later sieve parameters | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdWholeCellActions` | One parameter chosen at a representative works across the same closed coarse cell with explicit rescue and pair margins | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `ActualDwellSelectedRemainder` | The actual selected-prefix masks imply the original remaining-vector square condition and natural two-capacity allocation with coprime labelled products | Strict compilation; original-object stock kernel replay; complete 24-declaration types, inventory and transitive axiom audit |
| `Part3TransposedDispersion` | Exact transpose of the original signed error onto its genuine SW side, with the other coefficient second moment and the new smoothing and Poisson scales retained | Strict compilation; original-object stock kernel replay; complete 29-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9FiniteMean` | Literal ninth count is bounded by the true li main mass times the full same-weight upper density, with the coprime defect, signed Pan error, unit fibres and small-prime loss paid | Strict compilation; original-object stock kernel replay; complete 23-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdCompactCellCutoff` | New fixed-cutoff lookup evaluates the same nonlinear kernel on actual retained cells with positive third lower endpoint, with exact cell integrals and pointwise nonnegative kernel comparison only | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `Part3SignedDivisorDeletion` | The actual signed-error entry pays removal of beta indices dividing the original moving residue, preserves the true cleaned dispersion object and proves the cleaned large-gcd exception is zero | Strict compilation; original-object stock kernel replay; complete 36-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdCompactCellConvergence` | The actual h+mesh tail pays removal of whole cells; one fixed positive cutoff before buffer and grid recovers the original manuscript functional to every tolerance | Strict compilation; original-object stock kernel replay; complete 6-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9TrueLiMass` | The actual ninth li main mass has a genuine uniform leading-one upper transport to its same-product-image logarithmic reciprocal-totient mass, with the true positive power gap proved | Strict compilation; original-object stock kernel replay; complete 18-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9SwitchedUpperDensity` | The actual full same-coefficient ninth upper density has normalized upper bound eight, using the literal rounded Pan level, fixed Euler limit and produced canonical source contract | Strict compilation; original-object stock kernel replay; complete 22-declaration types, inventory and transitive axiom audit |
| `ActualPrimeIcoCellTestFunctions` | The actual prime-box test obeys a pointwise strict/weak affine-wall sandwich, retaining arithmetic boundary atoms; its current prerequisite objects are rebuilt and checked | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `ActualSelectedSubproductParameters` | The actual whole-cell pair margin pays alpha inflation, the critical interval and original full-support inflation before the concrete selected-remainder allocation | Strict compilation; original-object stock kernel replay; complete 25-declaration types, inventory and transitive axiom audit |
| `Part3TransposedZeroCovariance` | The actual transposed raw zero mode minus its literal primitive main term is the full grouped coprime covariance, paid by the original auxiliary SW family with true coefficient moments | Strict compilation; original-object stock kernel replay; complete 46-declaration types, inventory and transitive axiom audit |
| `Part3SmoothProgressionError` | The local Schwartz Poisson identity supplies one proved uniform O(1) smooth progression error for every positive scale and modulus and every signed residue | Strict compilation; original-object stock kernel replay; complete 14-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9HarmonicMean` | Literal original ninth product image has its proved true two-dimensional prime harmonic integral limit, preserving the mixed affine walls and original reciprocal-totient coefficients | Strict compilation; original-object stock kernel replay; complete 31-declaration types, inventory and transitive axiom audit |
| `Part3SmoothCoprimeError` | Actual finite Moebius inversion and a constructed CRT residue pay uniform smooth coprime and mixed progression errors with the same local Fourier mass and exact totient density | Strict compilation; original-object stock kernel replay; complete 33-declaration types, inventory and transitive axiom audit |
| `ActualTwoFactorRepairMonomials` | Actual full-vector repair in the below-one capacity case supplies all three original monomial bounds, with explicit positive margins paid by the real selected-pair parameters | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9OrdinaryUpperMean` | The actual ninth count has a genuine ordinary upper mean with factor eight and its true two-dimensional harmonic integral, with all errors paid after fixing the Pan exponent | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdCompactHarmonicProfile` | A continuous positive-clamp profile agrees exactly with the original cell kernel against prime harmonic density on the actual owned ordered region, with every wall retained pointwise | Strict compilation; original-object stock kernel replay; complete 26-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdCompactPrimeHarmonic` | Actual finite prime-box harmonic sums converge to the same retained-cell functional; cutoff, buffer and finite grid are fixed before the arithmetic target to recover the original ideal | Strict compilation; original-object stock kernel replay; complete 7-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9HarmonicSlices` | The actual mixed affine prime domain has exact moving half-open slices, with genuine compact-cube integrability and measure-preserving Fubini to the same two-dimensional harmonic integral | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `Part3TransposedPrimitiveU` | The literal transposed U minus its actual primitive main term is an exact finite sum of coprime counting errors with a proved uniform coefficient envelope | Strict compilation; original-object stock kernel replay; complete 10-declaration types, inventory and transitive axiom audit |
| `Part3PrimitiveZeroReal` | The full original factor-label primitive zero main term is proved Hermitian and real without coefficient assumptions or a changed normalization | Strict compilation; original-object stock kernel replay; complete 3-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon9HarmonicIntegral` | A proved logarithmic antiderivative evaluates the actual inner slice and gives the exact one-dimensional logarithmic dictionary for the original ninth harmonic integral | Strict compilation; original-object stock kernel replay; complete 10-declaration types, inventory and transitive axiom audit |
| `Part3TransposedPrimitiveUMoment` | The actual U residual pays both original alpha masses, full grouped gamma fibres and tau-six totient moments, then the genuine original beta L2 factor | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdOwnedLabelOrder` | Actual Ico-owned ordered cells force weakly ordered labels, invalidate reversed arithmetic atoms and give true floor power-endpoint integer boxes without ceil enlargement | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `ActualSelectedPairFactorization` | One deterministic actual selected-pair action handles both capacity cases and returns the original natural three factors and all three monomial targets using the same physical parameter | Strict compilation; original-object stock kernel replay; complete 5-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon8PrimeSource` | The literal eighth rough quotient is proved to be a prime or one from the original square-root and one-third cutoffs, giving the exact original prime/unit count dictionary | Strict compilation; original-object stock kernel replay; complete 20-declaration types, inventory and transitive axiom audit |
| `Part3TransposedGCDPoissonMask` | The same actual paired-gcd mask splits whole W, raw zero and the full nonzero Poisson remainder exactly, with the true original-alpha pair mass and raw-zero divisor moment paid | Strict compilation; original-object stock kernel replay; complete 24-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdDistinctPrimeHarmonic` | The actual strictly ordered prime selector has the same retained-cell harmonic limit, with repeated-prime wall loss proved by two arithmetic limits and the exact reciprocal-totient identity on distinct primes | Strict compilation; original-object stock kernel replay; complete 15-declaration types, inventory and transitive axiom audit |
| `Part3PairedAlphaDeletion` | Deleting actual old-alpha divisors of the signed moving residue has a proved finite error, every logarithmic payment and same-C0 auxiliary SW stability; the cleaned target remains separate | Strict compilation; original-object stock kernel replay; complete 47-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon8ProductPan` | The actual eighth zero-one product coefficient obeys its proved rounded two-thirds Pan window and true-li bounded aggregate majorant; units, the coprime main-term gate and signed sieve error remain separate | Strict compilation; original-object stock kernel replay; complete 34-declaration types, inventory and transitive axiom audit |
| `Part3TransposedPrimitiveUPayment` | The literal U residual after the true beta L2 factor has a derived X to the seven-fourths bound and every requested logarithmic decay, uniformly before actual atoms | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `Part3TransposedPrimitiveV` | The literal real V is the real part of the full actual mixed sum; P0 reality, active primitive residues and true mixed progression errors give its finite residual envelope | Strict compilation; original-object stock kernel replay; complete 16-declaration types, inventory and transitive axiom audit |
| `ActualPrimeTupleNormalization` | True prime-tuple product fibre multiplicity is at most the factorial; normalization gives one-bounded grouped coefficients and restores the original scalar exactly once | Strict compilation; original-object stock kernel replay; complete 8-declaration types, inventory and transitive axiom audit |
| `ActualExtendedThirdDistinctProductHarmonic` | Unique factorization and actual strict order give an injective original prefix-product carrier; arbitrary signed triple tests and the exact reciprocal totient transfer to the same product harmonic sum and original ideal | Strict compilation; original-object stock kernel replay; complete 24-declaration types, inventory and transitive axiom audit |

These 102 modules contain **2056 complete owned declarations**, including
private and generated declarations. The count is an inventory size, not
2056 independent major mathematical theorems.

The first, second and fifth literal current count means have complete
ordinary proofs with no analytic supplier premise.

The sixth actual ordinary count mean is also proved for E=False. Its
fixed-buffer arithmetic limit precedes the proved removal of the buffer;
the argument does not interchange these limits. It does not supply the
stronger causal h248 contribution or certify the adopted numerical L6.
The right-hand side remains the original full-rectangle sixth count;
the corrected strict inner product domain supplies a conservative lower
bound. This ordinary integral is distinct from the manuscript's adopted L6.

The third and fourth ordinary integral upper means are also proved
with the actual logarithmic integral normalization. This does not close
the stronger causal contributions or the complete eleven-term ledger.

The actual finite robust correction kernels are integrable on the
full original closed ordered domain. Their real integrals uniformly
approximate the literal unbuffered manuscript functional, with the
small-z tails and both changing boundary strips paid. This analytic
limit does not prove the same-policy arithmetic count mean.

The stronger causal contributions and the complete lower ledger remain open.

The ninth actual zero-one product coefficient now has its bounded Pan
aggregate and its genuine signed coprimality-defect budget proved. The
Pan modulus range is the ordinary square-root range. This does not pay
the higher physical level used by the adopted policy or complete the
eleven-term lower ledger.

The true logarithmic-integral main mass has its leading-one transport
to the same reciprocal-totient prime product mass. The actual ordinary
signed upper density has its proved normalized factor eight, with the
original rounded level and Euler normalization retained.

The actual ninth count now has a complete ordinary upper mean with
factor eight times its genuine two-dimensional harmonic integral. The
positive li mass and limiting integral are proved before multiplication;
no positivity assumption on the signed sieve density is used. The Pan
exponent is fixed before all error tolerances. The manuscript requires
the smaller coefficient currentK = 8452171/1250000 on the same harmonic
integral; the ordinary coefficient eight does not supply that estimate.
The stronger physical distribution level remains necessary.

The same ninth harmonic integral now has a proved moving-slice
Fubini decomposition and logarithmic antiderivative evaluation. This
identifies its exact one-dimensional manuscript expression; it does not
replay or replace a numerical integral enclosure.

A newly constructed compact-cell lookup recovers the same ideal
functional to every tolerance with a fixed positive third lower endpoint.
The cutoff is fixed before buffer and mesh. Removal of an entire cell
is paid by the actual full tail at cutoff plus mesh width. This compares
nonnegative integral kernels; identification and the arithmetic mean of
the new signed policy remain separate.

The original signed dispersion error has an exact transpose placing
the actual SW coefficient on the paired side. The other coefficient's
genuine divisor second moment, new smoothing scale and Poisson phases
are retained. This identity does not itself supply the zero-mode or
nonzero-frequency bounds needed by strong physical distribution.

The actual transposed raw zero mode minus its literal primitive main
term is now identified with the complete grouped coprime covariance.
The original auxiliary SW family pays that covariance, retaining all
factor labels, the tau-three fibre bound and original beta L2 logarithms.
The literal U/V residuals and nonzero frequencies are separate proof steps,
accepted only where listed with their own executed checks.

The actual finite prime-box harmonic sums also converge to the same
compact cell functional. Their pointwise strict/weak affine sandwich
retains prime atoms on ownership and ordering walls. Cutoff, buffer and
finite mesh are chosen before the arithmetic target, recovering the
original ideal to every tolerance. The signed first-exit arithmetic
density and original policy identification remain separate.

The literal eighth prime-or-unit source now has its genuine zero-one
product coefficient, rounded two-thirds Pan window and true-li bounded
aggregate majorant. This is a finite source and distribution step; the
original unit and small-prime losses, signed sieve errors and full eighth
ordinary mean require their own subsequent proofs.

Deleting actual original-alpha divisors of the moving signed residue
has a proved finite error and every logarithmic payment, with the same
auxiliary-SW constants preserved. The cleaned atom retains the original
beta and physical factor labels. Its full nonzero-frequency estimate
still needs the remaining region proofs.

Strictly ordered actual prime triples are now injective under their
original product by unique factorization. The finite sum is transported
exactly to that product image with its full reciprocal-totient weight and
the same recovered triple test. Its harmonic limit is the same original
functional, with all fixed cutoffs preceding N. No new factorial is
inserted and the signed first-exit counting dictionary remains separate.

## Candidates that must not be counted as completed proofs

The 31 unaccepted source candidates are listed with exact source
hashes in `verification/proof-continuation/2026-10-15/unaccepted-candidates.json`.
They are excluded from the accepted module/declaration inventory above.
Original failed attempts remain failures; replacement sources need their own checks.

* `Part3ReciprocalAPSupplier`: New target not executed; limited external prerequisite bootstrap stopped at a resource failure.
* `Certificates.PairedV2FullCertificate`: Not executed; requires the full original-strip chain, beyond the frozen baseline pilot.
* `ActualThirdPrefixTailIntegral`: Broad arithmetic tuple/profile bridge is not compiled; the separate canonical integral core is verified.
* `Part3PairedUpperEndpointSW`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualFrozenCapacitySlots`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualRoughVectorEndpointBudget`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualFrozenSelectedPairSlots`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualFrozenSlotCoefficientRegrouping`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualFrozenSelectedPairAssignment`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeSlotSquarefreeSymmetry`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedPrimitiveVMoment`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedPrimitiveVPayment`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedZeroPayment`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedZeroUVPayment`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeMultiLabelNormalization`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedLargeGCDFourier`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactResidualProfile`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeDisjointLabelProducts`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeFineLabelSortedSelector`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeFineWordMultiplicity`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeFineWordSlotRegrouping`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedModulusGCDZero`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualRosserOddBox`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeBoxEulerLower`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualRosserEvenBox`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedModulusProgression`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3TransposedDifferenceMoment`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactUpperRho`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactFrontier`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `FiniteUpperCarrierCore`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactPolicySaving`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.

The ordinary lower means above are baseline means. They do not prove the
manuscript's stronger causal h248 contribution, complete eleven-term lower
ledger, or adopted numerical constant.

The actual ideal cap, ordered integral, robust cell inequalities, fine-grid
coverage, Gamma approximation and boundary-strip passage are separate steps.
Each is accepted only when included in the executed-check table. The actual
branch/action licenses, full kernel convergence and same-policy arithmetic
count mean each require their own executed checks. Acceptance of one
component does not supply the others or discharge hUpper.

The complex CRT, finite Fourier, common Poisson and reciprocal-phase steps
are accepted only when individually listed in the executed-check table.
They do not prove zero-mode cancellation, aggregate gcd estimates or the
strong physical distribution bound. The real-component reduction pays a
finite complex-to-real cost; it is not a real distribution estimate. The
fibre majorant is tau_3 rather than one, and its logarithmic costs must be
retained by future estimates. The pointwise Buchstab comparison does not
pay actual arithmetic parent licensing or the full mean-value passage.

## External work reused

The fixed mathlib and `goldbach` dependency commits in `lake-manifest.json`
are unchanged. Existing prime harmonic measures, Rosser estimates, canonical
continuous sieve functions, Buchstab estimates and additive-character
orthogonality are reused rather than reimplemented.

In particular, source inspection of the pinned `goldbach` commit
`09b97db5764ade1246bfb77206baa1b124760958` found actual unconditional
`completeKloosterman_weil` and reciprocal progression suppliers in
`LiLiuPrereqFouvryCompleteWeil` and `LiLiuPrereqFouvryProgressionWeil`.
The selected 129-module `goldbach` source set passed a forbidden-token screen;
that screen does not constitute kernel replay, a compiled new consumer,
or the missing current strong distribution theorem.

The same fixed dependency also contains complete unconditional Fouvry C.2
and scaled-residue distribution endpoints. A fresh source audit follows
their full types, primitive definitions and 17 pinned source blobs. This
does not constitute imported-closure replay. Transposing the actual finite
double sum places the original alpha on the required Siegel-Walfisz side,
but does not prove the remaining hypotheses: the short-variable exponent
must be at most 1/10, the modulus coefficient must be well-factorable for
every level split, its support must lie below the actual C.2 level, and the
moving residue must stay within a fixed linear multiple of the local scale.
The current physical carrier and actual three-factor weights have not been
shown to satisfy these conditions. The full manuscript target is retained;
the endpoint is not claimed as a proof of the missing strong distribution.

The public pinned `Goldbach.Theorem.representation_lower_bound` supplies
the coefficient 0.67 on `liuSingularSeries * N / log(N)^2`. The project's
proved singular-series dictionary has no factor two, so this endpoint
cannot supply the current coefficient 1.96176252. The pinned Wu04/Wu08
research README explicitly says its final 1.8938 theorem and full signed
eleven-term ledger are incomplete. The exact public statement, pinned
source hashes and review boundary are recorded in
`20261016-chen-lower-reuse-scope.json`; this source inspection does not
claim new kernel acceptance or rule out future external candidates.

## Verification scope and resources

Successful owned-module audits compare the complete serialized declaration
inventory with the imported environment, export full types, reject unsafe,
partial and axiom declarations, and check transitive axioms are contained in
`propext`, `Classical.choice`, `Quot.sound`. Original bundled `leanchecker`
replays the actual owned object. This is not a claim that every external
imported declaration was independently replayed.

The historical runtime-v1 source walker recognized plain `import` headers
and omitted `public import` headers used by the pinned mathlib. Its recursive
closure sizes and recursive cache bindings are therefore incomplete. Actual
Lean compilation, stock replay and the Lean environment/type/axiom census
process the real imports; those executed owned-module checks are distinct
from this metadata limitation. No external cache is promoted to full
independent acceptance on the strength of that walker. Its original tools
and receipts are preserved, with the corrected inventory recorded separately.

One heavy process runs at a time with two Lean threads. The default Lean
budget is 4096 MiB. Measured import failures justified specific 6144 MiB
runs with an identity-bound 6656 MiB RSS monitor; the monitor is periodic,
not an operating-system hard cap. Resource failures remain failures.
No dependency pin, proof checker, analytic axiom or theorem premise was
weakened to obtain a pass.

The new initial-sieve density route removes the unrelated B8/aggregate
Mathlib path while retaining the same actual product, nu=1/phi and ceil L.
Its full advisory source-DAG comparison removes 4851 foreign modules.
The initial remainder route similarly removes 4841 foreign modules and
pays its AP budget directly with singularNormalization_lower. These are
source-import analyses, not independent external-object replay claims.

The finite U5 payment initially exceeded the budget through an unrelated
normalization import. Replacing that import by the existing explicit
`singularNormalization_lower` bound and a concrete logarithmic threshold
preserved the complete BV-paid count statement. Its final strict source
run peaked at about 4.49 GiB, compared with the earlier 6.36 GiB failure.
The compiler/checker owner serializes all heavy work through slot zero;
source and proof work continue independently between those jobs.

Exact successful receipts, logs, type exports and source/object hashes are
archived under `verification/proof-continuation/2026-10-15/`. Imported cache
objects used during development are not automatically promoted to complete
independent audit status. In particular, inherited remote-cache entries are
development-only even when their exact source/object hashes match.

## Next mathematical obligations

1. Complete the remaining actual ordinary/causal lower means with their
   genuine row coefficients and physical remainder budgets.
2. Pay the actual strong distribution/dispersion obligations with the full
   prime source, moduli, weights, primitive centre and errors retained.
3. Complete the adopted-selector density, tail and coefficient assembly for
   the real upper count; do not assume the final bound as a supplier.
4. Close all eleven corrected current lower mean terms, the actual paired
   deletion licenses and numerical constants, then discharge `hLower`.
5. Discharge `hUpper` for every fixed `1/2 < b < 1`, assemble the current
   main theorem and corollary, and run the full required integration gates.
