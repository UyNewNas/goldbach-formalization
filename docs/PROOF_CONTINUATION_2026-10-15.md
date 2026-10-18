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
| Strong physical distribution | Exact complex CRT, Fourier and Poisson dictionaries; ordinary transposed residuals and actual shared-factor pair/large-gcd whole-W bounds as accepted individually below | Shared-factor centered energy with its required 1/Q1 saving, complete conductor aggregation, remaining nonzero-frequency regions and the original full physical range |
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
| `FiniteUpperCarrierCore` | The same literal small-rough coefficient extends by zero to a covering rough carrier with exact preservation of its divisor sum, density, signed real-source coprime correction and distribution discrepancy | Strict compilation; original-object stock kernel replay; complete 20-declaration types, inventory and transitive axiom audit |
| `Part3TransposedLargeGCDFourier` | The original alpha cleanup and same-mask raw-zero subtraction give a genuine bound and every logarithmic payment for the paired large-gcd Fourier remainder after the original beta L2 factor; other gcd coordinates and the small remainder stay open | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `Part3TransposedModulusGCDZero` | The actual small-paired-gcd and large-physical-gcd mask retains compatibility before norm bounds and pays its genuine raw zero with original beta L2; whole W and the full nonzero part are separate | Strict compilation; original-object stock kernel replay; complete 35-declaration types, inventory and transitive axiom audit |
| `Part3TransposedPrimitiveVMoment` | The actual V residual pays the honest U-squared times cap logarithmic cost, retaining the original beta L2 moment and every physical modulus | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `ActualFrozenCapacitySlots` | One endpoint-vector greedy assignment freezes all original labelled slots on the full box, with natural product, capacity, coprimality and signed partition identities | Strict compilation; original-object stock kernel replay; complete 15-declaration types, inventory and transitive axiom audit |
| `Part3TransposedCanonicalReciprocalPhase` | The actual transposed CRT phase is exactly its canonical root, slow and reciprocal factors with the original signed residue, true physical lcm and every integer frequency retained; no slow-phase deletion or reciprocal energy estimate is assumed | Strict compilation; original-object stock kernel replay; complete 19-declaration types, inventory and transitive axiom audit |
| `ActualRoughVectorEndpointBudget` | Original rough-prime support pays the finite vector length and upper-endpoint inflation budget before the full-vector factorization | Strict compilation; original-object stock kernel replay; complete 11-declaration types, inventory and transitive axiom audit |
| `Part3TransposedModulusProgression` | The actual compatible physical gcd retains its own product progression before the full complex rows are bounded, giving a genuine whole-W divisor witness majorant with original smoothing and signed residue | Strict compilation; original-object stock kernel replay; complete 23-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon8SourceErrorBudget` | The literal eighth count splits exactly into large and small Goldbach-prime triples and unit fibres; actual injectivity and original product cutoffs pay both errors and prove their normalized limit is zero | Strict compilation; original-object stock kernel replay; complete 18-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon8CoprimeGateBudget` | The actual eighth product image pays its full non-coprime divisor mass using both genuine prime factors and totient supermultiplicativity; the original signed Rosser gate error has an internally derived negligible normalized cost uniform before cap, levels and positive moduli | Strict compilation; original-object stock kernel replay; complete 13-declaration types, inventory and transitive axiom audit |
| `Part3TransposedZeroPayment` | The original auxiliary SW exponent pays both actual fixed logarithm costs and the local Fourier mass, giving every requested decay for the actual beta L2 times raw-zero discrepancy | Strict compilation; original-object stock kernel replay; complete 2-declaration types, inventory and transitive axiom audit |
| `Part3TransposedPrimitiveVPayment` | Original medium geometry and fixed logarithm absorption pay the literal V residual and the combined U/V error after the actual beta L2 factor | Strict compilation; original-object stock kernel replay; complete 3-declaration types, inventory and transitive axiom audit |
| `Part3SharedFirstFactorDispersion` | The original signed entrance has a genuine joint Cauchy in beta and its first physical factor, retaining the full primitive first-factor carrier, honest extra Q1 outside factor, identical p in both CRT labels, same original-V cutoff, full physical lcm and complete signed Poisson series; the newly summed centered energy and its analytic payments remain open | Strict compilation; original-object stock kernel replay; complete 46-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon8FiniteMean` | One genuine actual eighth count bound retains its original product image, true li mass and same signed full upper density; the actual Pan aggregate, coprimality defect, literal units and small-prime loss are all paid with B fixed before epsilon and the threshold before every cap; its li transport and harmonic limit have separate exact-source acceptance | Strict compilation; original-object stock kernel replay; complete 29-declaration types, inventory and transitive axiom audit |
| `Part3TransposedDifferenceMoment` | The genuine off-diagonal tau-two difference moment and original beta L2 pay the entire same-mask large-physical-gcd nonzero Fourier contribution with a uniform scalar threshold before actual atoms and Y | Strict compilation; original-object stock kernel replay; complete 26-declaration types, inventory and transitive axiom audit |
| `ActualRosserOddBox` | Actual strictly decreasing odd prime tuples map injectively to their own boundary box with original prefix cubic gates and true natural ceiling endpoints | Strict compilation; original-object stock kernel replay; complete 19-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon8TrueLiMass` | The genuine real leading-one logarithmic-integral estimate transfers uniformly over the literal eighth product image to its same reciprocal-totient logarithmic mass, retaining its positive one-third gap; no harmonic or count mean is assumed | Strict compilation; original-object stock kernel replay; complete 12-declaration types, inventory and transitive axiom audit |
| `Part3TransposedZeroUVPayment` | All three actual primitive-center residuals are paid uniformly after the original beta L2 factor; the original signed error is reduced to its unchanged complete signed nonzero remainder | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `Part3SharedFirstFactorPairCount` | Actual ordered pairs retain both unit gates and their shared congruence for arbitrary positive composite first factors; genuine gcd cancellation, a finite inverse-square telescope and the harmonic moment give the full large-paired-gcd count including the diagonal, without asserting a W or Fourier energy bound | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `ActualRosserEvenBox` | Actual strictly decreasing even prime tuples map injectively to their own boundary box, retaining strict prefix gates and the terminal weak crossing in the true ceiling bounds | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `ActualFrozenSelectedPairSlots` | One frozen selected-pair slot partition supplies the same original three factors on the whole endpoint box and pays all three monomial targets with the actual parameters | Strict compilation; original-object stock kernel replay; complete 15-declaration types, inventory and transitive axiom audit |
| `CurrentChenUpsilon8HarmonicMean` | The literal eighth product image is exactly its original mixed strict and weak affine prime-box test, with a genuine harmonic limit equal to the unmodified two-dimensional integral; the ordinary coefficient and adopted causal budget remain separate | Strict compilation; original-object stock kernel replay; complete 19-declaration types, inventory and transitive axiom audit |
| `Part3SharedFirstFactorLargePairedGCDW` | The actual cleaned-alpha whole W under its original large-paired-gcd mask retains the shared first-factor congruence and full primitive carrier; genuine nonzero-shift divisor subpower, smoothed progression count and actual pair count prove the honest 16/4 bound, while raw zero, nonzero subtraction, outside payment and the full energy remain separate | Strict compilation; original-object stock kernel replay; complete 29-declaration types, inventory and transitive axiom audit |
| `SmallRoughDensityError` | The sign-sensitive small-weight attachment has a finite nonnegative density error controlled by absolute rough mass, while the original main density retains its signed coefficient; no sharp analytic budget is assumed | Strict compilation; original-object stock kernel replay; complete 4-declaration types, inventory and transitive axiom audit |
| `Part3SharedFirstFactorCharacterDictionary` | The full shared-first-factor zero covariance has an exact nonprincipal-character expansion with both auxiliary coprime sieves and actual full-modulus principal masses; all complex factors and the second inverse first factor remain, without an analytic large-sieve payment | Strict compilation; original-object stock kernel replay; complete 35-declaration types, inventory and transitive axiom audit |
| `ActualPrimePresieveSplit` | The actual capped target-deleted prime universe splits in its exact decreasing order at the real cutoff, and the same retained polynomial equals the fixed reciprocal-totient density with unit and squarefree endpoints retained | Strict compilation; original-object stock kernel replay; complete 9-declaration types, inventory and transitive axiom audit |
| `Part3SharedFirstFactorLowConductorSW` | The original uniform auxiliary SW family bounds one actual nonprincipal character sum at polylogarithmic conductor, retaining the full auxiliary k times delta divisor cost and uniform threshold; physical-label aggregation and the full zero-mode energy are separate | Strict compilation; original-object stock kernel replay; complete 16-declaration types, inventory and transitive axiom audit |
| `FirstExitGenericModuli` | Arbitrary literal first-exit policies have weight-independent fixed modulus supports and Mobius coefficients; genuine product injection retains leaf order and multiplicity before the exact signed density dictionary | Strict compilation; original-object stock kernel replay; complete 28-declaration types, inventory and transitive axiom audit |
| `FirstExitFrontierInvariants` | Actual retained-frontier histories recover their original mass, parity, selected labels and exact remaining smaller-prime carrier with the same target deletion, cap and strict endpoint | Strict compilation; original-object stock kernel replay; complete 19-declaration types, inventory and transitive axiom audit |
| `ActualPrimeBoxMass` | Actual target-deleted prime tuples in the literal box have the proved positive reciprocal-totient mass limit; no box integral or selected policy mean is assumed | Strict compilation; original-object stock kernel replay; complete 13-declaration types, inventory and transitive axiom audit |
| `ActualSmallRoughAttachment` | The same signed rough coefficient and actual small Rosser weights give a genuine physical majorant, support, unit coefficient bound and exact signed density sandwich; the absolute rough mass is used only for its explicit attachment error | Strict compilation; original-object stock kernel replay; complete 13-declaration types, inventory and transitive axiom audit |
| `SieveDimensionComparison` | The actual even-center finite sieve density has exact cap-split Euler quotients and a uniform comparison with all odd primes; this finite comparison does not assert an analytic Mertens dimension estimate | Strict compilation; original-object stock kernel replay; complete 40-declaration types, inventory and transitive axiom audit |
| `FirstExitOwnCubeSplice` | The exact difference of two literal policies is reindexed at their common before-test frontier, retaining every newly admitted candidate and each original continuation instead of assuming they agree | Strict compilation; original-object stock kernel replay; complete 10-declaration types, inventory and transitive axiom audit |
| `ActualPrimeBoxEulerLower` | Actual positive prime box mass times the proved Euler ratio gives the genuine lower limit with a single fixed threshold before the even target and cap | Strict compilation; original-object stock kernel replay; complete 14-declaration types, inventory and transitive axiom audit |
| `Part3SharedFirstFactorHighConductor` | Arbitrary bounded complex auxiliary-coprime polynomials retain the full imprimitive character level; exact Mobius and conductor grouping plus the sharp primitive coefficient-energy theorem give the genuine uniform high-conductor mean with the first R^(1-eta) saving intact; physical-label aggregation is separate | Strict compilation; original-object stock kernel replay; complete 85-declaration types, inventory and transitive axiom audit |
| `Part3SharedFirstFactorLowConductorAggregate` | The original uniform auxiliary SW family pays the full physical first factor and both original tail labels in the actual low-conductor zero covariance, retaining tau(p*v) costs by fixed divisor moments and the genuine 1/Q1 saving; high conductor and the complete distribution remain separate | Strict compilation; original-object stock kernel replay; complete 39-declaration types, inventory and transitive axiom audit |

These 138 modules contain **2794 complete owned declarations**, including
private and generated declarations. The count is an inventory size, not
2794 independent major mathematical theorems.

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
ordinary mean each require the separate executed checks listed below.

The literal eighth count has an exact large-prime, small-prime and
unit-fibre partition. Genuine source injectivity gives power bounds for
both discarded parts and a zero singular-normalized error limit. The full
eighth ordinary upper mean is a separate assembly and harmonic step.

The actual eighth non-coprime main-term gate is paid with both
genuine prime factors and the reciprocal-totient divisor estimate, without
assuming coprimality of the remaining cofactor. The original signed upper
Rosser coefficient is retained. Its negligible-error threshold precedes
every cap, level and selected positive-modulus set through N; this does
not supply the eighth leading mean or a density constant.

The literal eighth count is now bounded by its actual li main mass
times the same complete signed upper density, plus every positive multiple
of the original singular normalization. The genuine Pan exponent is fixed
before the tolerance, and the arithmetic threshold precedes every cap.
All four Pan, gate, small-prime and unit errors are paid internally. The
leading-one li transport and actual eighth harmonic limit have their own
exact-source acceptance below. Neither provides the adopted causal density.

The literal eighth true-li main mass has a uniform leading-one
transport to its same original reciprocal-totient logarithmic mass, with
the genuine one-third gap retained. This is a main-mass comparison, without
an assumed arithmetic count mean or a changed sieve coefficient.

The actual eighth logarithmic reciprocal-totient mass now converges
to its original two-dimensional harmonic integral. The mixed strict/weak
affine walls are retained pointwise on the arithmetic prime boxes; a
continuous clamp equals the original kernel on that exact region. Its
ordinary factor-eight density route still cannot supply the smaller
adopted causal row budget or currentK. This component does not assert the
complete eighth arithmetic count mean.

A separate, genuine joint Cauchy in the original beta and first
physical factor keeps that same factor p on both squared-row labels. The
full primitive p carrier, same-C0 auxiliary SW family, original V cutoff,
signed residue, full lcm and every integer Poisson frequency are literal.
The outside factor has the honest extra Q1; the new summed centered energy
must be bounded at scale V U^2 / Q1. Old independent-first-factor zero/U/V,
gcd-region and reciprocal estimates do not automatically pay this energy.
In particular gcd(p v1,p v2)=p gcd(v1,v2), so the old small full-gcd region
cannot simply be transferred to a residual-gcd partition. Slow phases,
the new energy and the complete restricted medium bound remain open.

Actual ordered pairs retain their unit gates and common congruence
for every positive first factor, including composites. Gcd cancellation,
a finite inverse-square telescope and the harmonic moment bound the full
large-paired-gcd pair count, including its diagonal. Its analytic consumers
are accepted individually below.

The actual cleaned-alpha whole W under its original large-paired-gcd
mask has the proved bound C X^epsilon (4 V/Q1 + 1) times
(16 U^2/Y + 4 Q1 U (1 + log(2 U))). The same first factor, complete primitive
carrier, complex coefficients and signed residue remain. This pays that
masked whole W only: raw-zero subtraction, outside-factor payment, the
remaining regions and the full centered energy are separate obligations.

The full actual shared-factor zero covariance has an exact
nonprincipal-character expansion. Both auxiliary coprime sieves, the
full-modulus principal masses, complex conjugates and coefficient
V/(p L phi(p D)) remain. This finite dictionary supplies no conductor
large-sieve bound or completed zero-mode payment.

At polylogarithmic conductor, the original uniform auxiliary SW
family bounds one actual nonprincipal character sum with its constants
chosen before the atom, auxiliary level and character. Lowering the
conductor keeps every nonunit in k*delta, so the true divisor penalty is
tau(k*delta)^C0, or tau(p*v)^C0 at the actual shared-factor specialization.
The full physical low-conductor aggregate and generic high-conductor mean
have their separate acceptance records below; their residual consumers
and complete zero-mode assembly remain separate.

Deleting actual original-alpha divisors of the moving signed residue
has a proved finite error and every logarithmic payment, with the same
auxiliary-SW constants preserved. The cleaned atom retains the original
beta and physical factor labels. Its full nonzero-frequency estimate
still needs the remaining region proofs.

The entire same-mask large-physical-gcd nonzero Fourier contribution
is paid after original beta L2. Actual diagonal and off-diagonal divisor
moments supply the whole-W bound, and same-mask raw zero is also paid.
The both-small region, its reciprocal and slow phases, and the full
restricted medium estimate remain open.

Strictly ordered actual prime triples are now injective under their
original product by unique factorization. The finite sum is transported
exactly to that product image with its full reciprocal-totient weight and
the same recovered triple test. Its harmonic limit is the same original
functional, with all fixed cutoffs preceding N. No new factorial is
inserted and the signed first-exit counting dictionary remains separate.

The actual paired large-gcd Fourier remainder is paid after the
original beta L2 factor, including the same-mask raw-zero subtraction and
the signed-residue cleanup. This covers that gcd region only; the other
regions and the full physical distribution endpoint remain open.

Both literal primitive-center residuals U-P0 and V-P0 are paid after
the actual original beta L2 factor, with every requested real logarithmic
decay. The honest V estimate keeps two alpha masses and the full physical
cap; original medium geometry pays them. Nonzero frequencies and the
complete physical distribution endpoint remain open.

The full generic high-conductor mean is proved for arbitrary bounded
complex coefficients, with the original auxiliary coprime mask and full
imprimitive character level. Exact Mobius/conductor regrouping and the
sharp primitive coefficient energy retain Q N^2/R^(1-eta) without a global
Q^eta loss in that term. The constant precedes all varying parameters.
The actual physical tail-label aggregation is a separate consumer.

The low-conductor zero covariance is now bounded after summing the
full physical first factor and both original ordered tail labels. The
original auxiliary SW family supplies the estimate, with the full
tau(p*v) cost paid by fixed divisor moments and the genuine 1/Q1 saving.
This is low conductor on every residual gcd, not the full zero estimate.

The next-selection enumeration uses an explicit List.rec implementation
with unconditional nil/cons equations. Its complete new generated census
passes the unchanged safety audit. The former unsafe-helper INCOMPLETE
attempt remains archived and is not retrospectively accepted.

The earlier primitive U/V payments use the original beta L2 outside
factor. Their reuse in the shared-first-factor setting, with the extra
primitive gamma1 L2 factor and the p sum, needs a genuine additional
aggregation and payment. A raw-zero conductor decomposition alone does
not establish the complete centered energy or physical distribution.

## Candidates that must not be counted as completed proofs

The 21 unaccepted source candidates are listed with exact source
hashes in `verification/proof-continuation/2026-10-15/unaccepted-candidates.json`.
They are excluded from the accepted module/declaration inventory above.
Original failed attempts remain failures; replacement sources need their own checks.

* `Part3ReciprocalAPSupplier`: New target not executed; limited external prerequisite bootstrap stopped at a resource failure.
* `Certificates.PairedV2FullCertificate`: Not executed; requires the full original-strip chain, beyond the frozen baseline pilot.
* `ActualThirdPrefixTailIntegral`: Broad arithmetic tuple/profile bridge is not compiled; the separate canonical integral core is verified.
* `Part3PairedUpperEndpointSW`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualFrozenSlotCoefficientRegrouping`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualFrozenSelectedPairAssignment`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeSlotSquarefreeSymmetry`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeMultiLabelNormalization`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactResidualProfile`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeDisjointLabelProducts`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeFineLabelSortedSelector`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeFineWordMultiplicity`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualPrimeFineWordSlotRegrouping`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactUpperRho`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactFrontier`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactPolicySaving`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdInitialCutoff`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualUpperPolicyFiniteBridge`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3SharedFirstFactorLargeResidualZero`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `Part3SharedFirstFactorSmallResidualHighConductorZero`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.
* `ActualExtendedThirdCompactSignedDensityLimit`: Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.

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
