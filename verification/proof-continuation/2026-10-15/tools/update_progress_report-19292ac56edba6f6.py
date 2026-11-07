from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'

manifest = json.loads((DEST / 'manifest.json').read_text(encoding='utf-8'))
candidates = json.loads((DEST / 'unaccepted-candidates.json').read_text(encoding='utf-8'))
path = ROOT / 'docs/PROOF_CONTINUATION_2026-10-15.md'
text = path.read_text(encoding='utf-8')
text = text.replace(
    '| Strong physical distribution | Exact complex CRT, Fourier, Poisson and transposed covariance identities; accepted residual estimates are listed individually below | The full nonzero-frequency bound on the original physical range, including all remaining gcd regions |',
    '| Strong physical distribution | Exact complex CRT, Fourier and Poisson dictionaries; ordinary transposed residuals and actual shared-factor pair/large-gcd whole-W bounds as accepted individually below | Shared-factor centered energy with its required 1/Q1 saving, complete conductor aggregation, remaining nonzero-frequency regions and the original full physical range |')
# Keep the core overview consistent with accepted ordinary means and shared-factor payments.
text = re.sub('(?m)^\\| Chen lower ledger \\|.*$', '| Chen lower ledger | Actual ordinary means for the first six rows; ordinary eighth and ninth upper means with coefficient eight | Original selected masks, stronger causal contributions, remaining seventh/tenth/eleventh means and the complete eleven-term ledger |', text)
text = re.sub('(?m)^\\| Strong physical distribution \\|.*$', '| Strong physical distribution | Exact complex CRT/Fourier/Poisson dictionaries; shared-first-factor zero covariance and U/V energy payments under the original auxiliary SW input; reciprocal-phase identities and large-gcd/large-supported-part nonzero payments | A genuine estimate for the retained small paired-gcd/supported-part spectral core, remaining tail-gcd/frequency costs and final assembly over the original full physical range |', text)
descriptions = {
    **{name: description for name, description in re.findall(
        r'^\| `([^`]+)` \| ([^|]+) \|', text, re.MULTILINE)},
    'Part3CommonPoisson': 'Actual common smooth progression to integer lattice, Schwartz Poisson and the full nonzero-frequency remainder, retaining the true complex labels and V/U',
    'ActualExtendedThirdDyadicCoverage': 'Actual dyadic ownership, unique retained coverage away from the displayed stopping strip and uniform fine-grid bounds',
    'CurrentChenRosserEndpointDictionary': 'Exact actual initial-sieve product, nu=1/phi, Euler product and ceil-level dictionary; uniform genuine Mertens local bound',
    'CurrentChenRosserLowerRectangle': 'Uniform canonical AllDepth lower estimate on the actual initial sieve; rounding, sourceSigma and adaptive-depth error paid',
    'CurrentChenFixedEulerNormalization': 'Actual target-prime-deleted Euler product at fixed positive power cutoff has the genuine 2 exp(-gamma)/a normalized limit',
    'CurrentChenPairDensity': 'Uniform one-sided normalized density bound for every genuine rounded fifth-row level',
    'CurrentChenUpsilon5OrdinaryMean': 'Actual fifth-row ordinary count mean with the genuine moving harmonic integral and complete BV/centre payment',
    'Part3ComplexCRTConsumer': 'Actual complex W becomes a constructed lcm CRT progression, with incompatible/inactive labels and the primitive-centre V/U retained',
    'Part3ComplexCRTFiniteFourier': 'Same common finite source split into the actual mass/lcm zero mode and complete nonzero Fourier term, retaining V/U',
    'Part3CommonSmoothCutoff': 'One genuine smooth bump, Schwartz Fourier decay and its actual medium-atom common smooth Cauchy consumer',
    'ActualExtendedThirdIdealCap': 'Literal eight-branch/pair-gated ideal cap: measurability and finite vanishing noncompact canonical tail',
    'ActualExtendedThirdOrderedIntegral': 'Actual clamped correction kernel: measurability, Fin-3 Tonelli to nested integration, integrability and real integral identification',
    'ActualExtendedThirdClosedIntegral': 'Actual affine diagonal null wall pays the closed ordered domain; old-cube equality is paid by the clamped lower factor',
    'ActualExtendedThirdPhysicalCell': 'Literal closed ordered robust Gamma cells: retention/transition walls, two whole-cell pair gates, ideal domination and uniform small-z margin',
    'CurrentChenInitialRosserRemainder': 'Actual initial count above the same Rosser density with complete ordinary BV and centre errors paid',
    'CurrentChenOrdinaryInitialMean': 'Actual initial ordinary mean at full Q+1 level for every fixed 0<a<1/4, using canonical f at the genuine ratio 1/(2a)',
    'CurrentChenOrdinaryInitialLedger': 'The first two actual current Upsilon rows receive their full ordinary means at the original current cutoffs',
    'CurrentChenUpsilon6OrdinarySource': 'Literal corrected inner sixth selector and actual quotient counts, with only nonnegative counts dropped and E=False scope retained',
    'CurrentChenUpsilon6FiniteMean': 'One BV exponent pays all errors for every actual sixth-row subselector chosen after N, retaining the full physical moduli and row coefficients',
    'CurrentChenUpsilon6OrdinaryMean': 'Actual unmasked sixth-row ordinary mean: fixed-buffer arithmetic limit followed by the proved buffer-removal integral limit',
    'CurrentChenRosserUpperEndpointDictionary': 'Exact actual upper Rosser weight, reciprocal-totient coefficient, product and ceil-level dictionary',
    'CurrentChenRosserUpperRectangle': 'Uniform genuine canonical AllDepth upper factor for every s>1, with all actual level and adaptive-depth errors paid',
    'CurrentChenQuotientUpperRosser': 'Actual quotient count upper Rosser bound with the complete physical-modulus AP and centre errors',
    'CurrentChenSinglePrimeUpperFiniteMean': 'One ordinary BV budget pays every actual third-row subselector and the genuine fourth-row finite upper count',
    'Part3RealComponentReduction': 'Exact 32 real-component expansion of the actual five complex coefficients; same family-uniform SW constants and explicit square cost',
    'Part3FactorFiberDivisor': 'Actual physical-modulus factor fibres retain all labels, with a proved tau_3 majorant and explicit logarithmic second-moment costs',
    'ActualExtendedThirdFirstCubeMargin': 'Actual retained robust cap has the displayed positive first-cube margin',
    'ActualExtendedThirdGammaApproximation': 'Literal robust Gamma approximates the same eight-branch ideal cap outside the explicitly paid transition and stopping strips',
    'ActualExtendedThirdLowerFactorRegularity': 'The same canonical clamped lower factor is globally continuous, nonnegative and bounded by 1/(2 exp(gamma))',
    'CurrentChenTrueLiNormalization': 'Genuine leading-one normalization of the actual logarithmic integral, proved without an asymptotic supplier premise',
    'CurrentChenSinglePrimeHarmonicMean': 'Actual single-prime reciprocal-totient sums with moving row profiles have their genuine harmonic integral limits',
    'CurrentChenSinglePrimeUpperDensity': 'Actual rounded single-prime upper Rosser density with canonical upper factor and fixed Euler normalization',
    'CurrentChenUpsilon34OrdinaryUpperMean': 'Literal third- and fourth-row ordinary upper count means with their original cutoffs and complete error budgets',
    'Part3CanonicalReciprocalData': 'Canonical finite gcd-factor data constructed from actual compatible CRT row labels, including the true lcm reconstruction and phase-unit gates',
    'ActualExtendedThirdFinitePhysicalKernel': 'Literal finite retained-cell lookup, measurable actual clamped kernel, compact bound and uniform canonical nested small-z tail',
    'ActualExtendedThirdStripIntegral': 'Actual transition/stopping strips have vanishing compact-kernel mass with the displayed uniform volume and threshold order',
    'Part3CanonicalReciprocalPhase': 'Exact three-phase dictionary for the actual signed CRT residue and all integer Poisson frequencies, retaining the slow term, full complex labels and primitive V/U',
    'ActualExtendedThirdFiniteTailIntegral': 'Actual finite physical lookup has a genuine tuple-space Tonelli and closed-order tail bridge to the uniform canonical small-z bound',
    'ActualExtendedThirdBoundaryLoss': 'Full actual physical and ideal transition/stopping-strip masses vanish after paying the compact and uniform small-z parts in the displayed threshold order',
    'ActualExtendedThirdLeastWinningIndex': 'Deterministic least maximizing actual cell branch; real infimum and tie-priority arguments exclude failed-pair and unsupported p2 choices',
    'ActualExtendedThirdActionParameters': 'Actual selected branch parameters in the required interval, with the true rescue equality dispatch and pair gate/endpoint margins',
    'ActualExtendedThirdWholeCellActions': 'One parameter chosen at a representative works across the same closed coarse cell with explicit rescue and pair margins',
    'ActualTwoCapacityGreedy': 'Deterministic prefer-left allocation under the original-vector prefix-square condition, retaining natural products, labels, capacities and full-vector repair',
    'Part3CleanBetaLargeGCDMajorant': 'Actual large-gcd W splits into a clean-beta divisor majorant and the complete explicit signed-divisor exception',
    'Part3PolynomialResidueDivisorBound': 'Genuine divisor subpower bound pays the actual moving polynomial residue in the original scale, retaining clean-pair mass and the exception',
    'CurrentChenUpsilon9PrimeSource': 'Literal ninth source is exactly a prime-triple part plus the actual unit fibres, proved from its genuine square-root rough cutoff',
    'CurrentChenUpsilon9UnitBudget': 'Actual ninth unit fibres have a concrete 4 N^(92/125) bound and a proved negligible singular-normalized contribution',
    'ActualExtendedThirdCompactKernelApproximation': 'The actual finite kernel uniformly approximates the unbuffered ideal kernel off the exact two strips, paying both level changes and a genuine canonical modulus',
    'ActualExtendedThirdKernelL1Convergence': 'Whole-domain absolute L1 error of the actual finite lookup against the unbuffered ideal kernel tends to zero with one cutoff before all buffers and meshes',
    'ActualDwellSelectedRemainder': 'The actual selected-prefix masks imply the original remaining-vector square condition and natural two-capacity allocation with coprime labelled products',
    'ActualSelectedSubproductParameters': 'The actual whole-cell pair margin pays alpha inflation, the critical interval and original full-support inflation before the concrete selected-remainder allocation',
    'CurrentChenUpsilon9ProductCoefficient': 'Literal ordered prime-pair products give a modulus-independent zero-one coefficient on the genuine power interval, retaining the original quotient and unit fibres',
    'Part3ActualLargeGCDBetaMass': 'Actual clean complex beta norms have a proved large-gcd pair-mass bound at the original length, with explicit logarithmic cost and the original exception retained',
    'ActualExtendedThirdFunctionalConvergence': 'Full-domain integrability of the actual physical and ideal kernels, and uniform convergence of the finite-policy real integral to the literal unbuffered manuscript functional',
    'CurrentChenUpsilon9CoprimeGateBudget': 'Actual signed upper Rosser coprimality defect of the same zero-one ninth coefficient has a proved N^(106/125) log(N)^2 budget and a negligible singular-normalized contribution',
    'ActualTwoFactorRepairMonomials': 'Actual full-vector repair in the below-one capacity case supplies all three original monomial bounds, with explicit positive margins paid by the real selected-pair parameters',
    'ActualSelectedPairFactorization': 'One deterministic actual selected-pair action handles both capacity cases and returns the original natural three factors and all three monomial targets using the same physical parameter',
    'Part3SignedDivisorDeletion': 'The actual signed-error entry pays removal of beta indices dividing the original moving residue, preserves the true cleaned dispersion object and proves the cleaned large-gcd exception is zero',
    'CurrentChenUpsilon9PanAggregate': 'The actual modulus-independent zero-one ninth coefficient receives a proved bounded Pan aggregate and exact coprime-defect decomposition, with one fixed B before all later sieve parameters',
    'ActualExtendedThirdFiniteCellIntegral': 'Exact finite decomposition of the actual nonlinear retained-cell kernel and its genuine integrable ordered cell integrals, with uniform convergence to the literal manuscript functional',
    'Part3TransposedDispersion': 'Exact transpose of the original signed error onto its genuine SW side, with the other coefficient second moment and the new smoothing and Poisson scales retained',
    'Part3PairedUpperEndpointSW': 'Global polynomial-endpoint SW bounds on the actual transposed paired coefficient, paying bounded scales and uniform constants from the original auxiliary SW family',
    'ActualPrimeTupleNormalization': 'True prime-tuple product fibre multiplicity is at most the factorial; normalization gives one-bounded grouped coefficients and restores the original scalar exactly once',
    'ActualFrozenCapacitySlots': 'One endpoint-vector greedy assignment freezes all original labelled slots on the full box, with natural product, capacity, coprimality and signed partition identities',
    'ActualRoughVectorEndpointBudget': 'Original rough-prime support pays the finite vector length and upper-endpoint inflation budget before the full-vector factorization',
    'CurrentChenUpsilon9FiniteMean': 'Literal ninth count is bounded by the true li main mass times the full same-weight upper density, with the coprime defect, signed Pan error, unit fibres and small-prime loss paid',
    'ActualFrozenSelectedPairSlots': 'One frozen selected-pair slot partition supplies the same original three factors on the whole endpoint box and pays all three monomial targets with the actual parameters',
    'CurrentChenUpsilon9TrueLiMass': 'The actual ninth li main mass has a genuine uniform leading-one upper transport to its same-product-image logarithmic reciprocal-totient mass, with the true positive power gap proved',
    'ActualExtendedThirdCompactCellCutoff': 'New fixed-cutoff lookup evaluates the same nonlinear kernel on actual retained cells with positive third lower endpoint, with exact cell integrals and pointwise nonnegative kernel comparison only',
    'ActualExtendedThirdCompactCellConvergence': 'The actual h+mesh tail pays removal of whole cells; one fixed positive cutoff before buffer and grid recovers the original manuscript functional to every tolerance',
    'ActualFrozenSlotCoefficientRegrouping': 'Exact full Cartesian prime-slot box regrouping through the same frozen slot partition and factorial-normalized coefficient fibres; original first-exit ordering and squarefree identification remain separate',
    'CurrentChenUpsilon9HarmonicMean': 'Literal original ninth product image has its proved true two-dimensional prime harmonic integral limit, preserving the mixed affine walls and original reciprocal-totient coefficients',
    'CurrentChenUpsilon9SwitchedUpperDensity': 'The actual full same-coefficient ninth upper density has normalized upper bound eight, using the literal rounded Pan level, fixed Euler limit and produced canonical source contract',
    'ActualFrozenSelectedPairAssignment': 'Finite bounded slot-word partition preserves each full signed Cartesian box and its same computed allocation; membership fibres do not assert literal ordered-list equality or the original rho dictionary',
    'ActualPrimeSlotSquarefreeSymmetry': 'Literal Moebius product weight vanishes on repeated prime tuples; a single repeated-label block has the exact factorial fibre and original normalization, with the full multi-label policy dictionary separate',
    'ActualPrimeIcoCellTestFunctions': 'The actual prime-box test obeys a pointwise strict/weak affine-wall sandwich, retaining arithmetic boundary atoms; its current prerequisite objects are rebuilt and checked',
    'Part3TransposedZeroCovariance': 'The actual transposed raw zero mode minus its literal primitive main term is the full grouped coprime covariance, paid by the original auxiliary SW family with true coefficient moments',
    'Part3SmoothProgressionError': 'The local Schwartz Poisson identity supplies one proved uniform O(1) smooth progression error for every positive scale and modulus and every signed residue',
    'Part3SmoothCoprimeError': 'Actual finite Moebius inversion and a constructed CRT residue pay uniform smooth coprime and mixed progression errors with the same local Fourier mass and exact totient density',
    'ActualExtendedThirdCompactHarmonicProfile': 'A continuous positive-clamp profile agrees exactly with the original cell kernel against prime harmonic density on the actual owned ordered region, with every wall retained pointwise',
    'ActualExtendedThirdCompactPrimeHarmonic': 'Actual finite prime-box harmonic sums converge to the same retained-cell functional; cutoff, buffer and finite grid are fixed before the arithmetic target to recover the original ideal',
    'Part3PrimitiveZeroReal': 'The full original factor-label primitive zero main term is proved Hermitian and real without coefficient assumptions or a changed normalization',
    'Part3TransposedPrimitiveU': 'The literal transposed U minus its actual primitive main term is an exact finite sum of coprime counting errors with a proved uniform coefficient envelope',
    'Part3TransposedPrimitiveUMoment': 'The actual U residual pays both original alpha masses, full grouped gamma fibres and tau-six totient moments, then the genuine original beta L2 factor',
    'Part3TransposedPrimitiveUPayment': 'The literal U residual after the true beta L2 factor has a derived X to the seven-fourths bound and every requested logarithmic decay, uniformly before actual atoms',
    'Part3TransposedPrimitiveV': 'The literal real V is the real part of the full actual mixed sum; P0 reality, active primitive residues and true mixed progression errors give its finite residual envelope',
    'Part3TransposedPrimitiveVMoment': 'The actual V residual pays the honest U-squared times cap logarithmic cost, retaining the original beta L2 moment and every physical modulus',
    'Part3TransposedPrimitiveVPayment': 'Original medium geometry and fixed logarithm absorption pay the literal V residual and the combined U/V error after the actual beta L2 factor',
    'Part3PairedAlphaDeletion': 'Deleting actual old-alpha divisors of the signed moving residue has a proved finite error, every logarithmic payment and same-C0 auxiliary SW stability; the cleaned target remains separate',
    'CurrentChenUpsilon9OrdinaryUpperMean': 'The actual ninth count has a genuine ordinary upper mean with factor eight and its true two-dimensional harmonic integral, with all errors paid after fixing the Pan exponent',
    'CurrentChenUpsilon9HarmonicSlices': 'The actual mixed affine prime domain has exact moving half-open slices, with genuine compact-cube integrability and measure-preserving Fubini to the same two-dimensional harmonic integral',
    'CurrentChenUpsilon9HarmonicIntegral': 'A proved logarithmic antiderivative evaluates the actual inner slice and gives the exact one-dimensional logarithmic dictionary for the original ninth harmonic integral',
    'Part3TransposedZeroPayment': 'The original auxiliary SW exponent pays both actual fixed logarithm costs and the local Fourier mass, giving every requested decay for the actual beta L2 times raw-zero discrepancy',
    'Part3TransposedZeroUVPayment': 'All three actual primitive-center residuals are paid uniformly after the original beta L2 factor; the original signed error is reduced to its unchanged complete signed nonzero remainder',
    'Part3TransposedGCDPoissonMask': 'The same actual paired-gcd mask splits whole W, raw zero and the full nonzero Poisson remainder exactly, with the true original-alpha pair mass and raw-zero divisor moment paid',
    'ActualExtendedThirdOwnedLabelOrder': 'Actual Ico-owned ordered cells force weakly ordered labels, invalidate reversed arithmetic atoms and give true floor power-endpoint integer boxes without ceil enlargement',
    'ActualExtendedThirdDistinctPrimeHarmonic': 'The actual strictly ordered prime selector has the same retained-cell harmonic limit, with repeated-prime wall loss proved by two arithmetic limits and the exact reciprocal-totient identity on distinct primes',
    'ActualExtendedThirdDistinctProductHarmonic': 'Unique factorization and actual strict order give an injective original prefix-product carrier; arbitrary signed triple tests and the exact reciprocal totient transfer to the same product harmonic sum and original ideal',
    'CurrentChenUpsilon8PrimeSource': 'The literal eighth rough quotient is proved to be a prime or one from the original square-root and one-third cutoffs, giving the exact original prime/unit count dictionary',
    'CurrentChenUpsilon8ProductPan': 'The actual eighth zero-one product coefficient obeys its proved rounded two-thirds Pan window and true-li bounded aggregate majorant; units, the coprime main-term gate and signed sieve error remain separate',
    'ActualPrimeMultiLabelNormalization': 'The literal full-product Mobius coefficient removes nonsquarefree blocks before each original repeated-label factorial is cancelled exactly once; all block-product vectors remain, without an assumed product uniqueness dictionary',
    'Part3TransposedLargeGCDFourier': 'The original alpha cleanup and same-mask raw-zero subtraction give a genuine bound and every logarithmic payment for the paired large-gcd Fourier remainder after the original beta L2 factor; other gcd coordinates and the small remainder stay open',
    'ActualExtendedThirdCompactResidualProfile': 'Actual original-cap lower-density differences converge to the same retained-cell harmonic functional; strict gate failures vanish pointwise and an internal enlarged cap is restored exactly to N on every selected atom. Full signed rho splice and counting error remain open',
    'ActualPrimeDisjointLabelProducts': 'Unique factorization and actual disjoint half-open label intervals give injective block-product carriers while retaining the full product Mobius coefficient and original repeated-label factorial',
    'ActualPrimeFineLabelSortedSelector': 'Sorting within actual disjoint fine-label blocks gives the unique strictly ordered squarefree product representative and exact signed factorial dictionary without assuming a per-tuple allocation',
    'ActualPrimeFineWordMultiplicity': 'The original weakly decreasing fine-label word computes its run blocks and its literal product of repeated-label factorials, giving the original word dictionary without a caller block decomposition',
    'ActualPrimeFineWordSlotRegrouping': 'The same original fine word and fixed slot allocation regroup with the original c over M_J and joint Mobius of the full product retained; coefficient separability and rough label support remain open',
    'Part3TransposedModulusGCDZero': 'The actual small-paired-gcd and large-physical-gcd mask retains compatibility before norm bounds and pays its genuine raw zero with original beta L2; whole W and the full nonzero part are separate',
    'ActualRosserOddBox': 'Actual strictly decreasing odd prime tuples map injectively to their own boundary box with original prefix cubic gates and true natural ceiling endpoints',
    'ActualPrimeBoxEulerLower': 'Actual positive prime box mass times the proved Euler ratio gives the genuine lower limit with a single fixed threshold before the even target and cap',
    'ActualRosserEvenBox': 'Actual strictly decreasing even prime tuples map injectively to their own boundary box, retaining strict prefix gates and the terminal weak crossing in the true ceiling bounds',
    'Part3TransposedModulusProgression': 'The actual compatible physical gcd retains its own product progression before the full complex rows are bounded, giving a genuine whole-W divisor witness majorant with original smoothing and signed residue',
    'Part3TransposedDifferenceMoment': 'The genuine off-diagonal tau-two difference moment and original beta L2 pay the entire same-mask large-physical-gcd nonzero Fourier contribution with a uniform scalar threshold before actual atoms and Y',
    'ActualExtendedThirdCompactUpperRho': 'One concrete initial dyadic first-stop policy and frozen third-cell extension define the actual original physical rho; inherited first admission and finite attachment, support and majorant identities are proved',
    'ActualExtendedThirdCompactFrontier': 'The original rank-two before-test candidate frontier filtered by an adopted owned cell equals its actual strictly ordered prime carrier, retaining the original cap and exact signed reciprocal-totient product sum',
    'FiniteUpperCarrierCore': 'The same literal small-rough coefficient extends by zero to a covering rough carrier with exact preservation of its divisor sum, density, signed real-source coprime correction and distribution discrepancy',
    'ActualExtendedThirdCompactPolicySaving': 'The actual same-policy full third-test polynomial correction equals the existing original-cap gated lower-density difference sum, retaining the rank-two before-test frontier, unique owned cells, negative third sign and concrete dyadic-first-stop baseline',
    'Part3SharedFirstFactorDispersion': 'The original signed entrance has a genuine joint Cauchy in beta and its first physical factor, retaining the full primitive first-factor carrier, honest extra Q1 outside factor, identical p in both CRT labels, same original-V cutoff, full physical lcm and complete signed Poisson series; the newly summed centered energy and its analytic payments remain open',
    'Part3TransposedCanonicalReciprocalPhase': 'The actual transposed CRT phase is exactly its canonical root, slow and reciprocal factors with the original signed residue, true physical lcm and every integer frequency retained; no slow-phase deletion or reciprocal energy estimate is assumed',
    'CurrentChenUpsilon8SourceErrorBudget': 'The literal eighth count splits exactly into large and small Goldbach-prime triples and unit fibres; actual injectivity and original product cutoffs pay both errors and prove their normalized limit is zero',
    'CurrentChenUpsilon8CoprimeGateBudget': 'The actual eighth product image pays its full non-coprime divisor mass using both genuine prime factors and totient supermultiplicativity; the original signed Rosser gate error has an internally derived negligible normalized cost uniform before cap, levels and positive moduli',
    'ActualExtendedThirdInitialCutoff': 'The original initial dyadic first-stop polynomial equals the literal ordinary plus density at its exact floor-grid prime cutoff, retaining zero cutoff exponents, strict endpoints, original cap N and all old-level product and cubic tests; its asymptotic mean remains separate',
    'Part3SharedFirstFactorPairCount': 'Actual ordered pairs retain both unit gates and their shared congruence for arbitrary positive composite first factors; genuine gcd cancellation, a finite inverse-square telescope and the harmonic moment give the full large-paired-gcd count including the diagonal, without asserting a W or Fourier energy bound',
    'CurrentChenUpsilon8FiniteMean': 'One genuine actual eighth count bound retains its original product image, true li mass and same signed full upper density; the actual Pan aggregate, coprimality defect, literal units and small-prime loss are all paid with B fixed before epsilon and the threshold before every cap; its li transport and harmonic limit have separate exact-source acceptance',
    'Part3SharedFirstFactorLargePairedGCDW': 'The actual cleaned-alpha whole W under its original large-paired-gcd mask retains the shared first-factor congruence and full primitive carrier; genuine nonzero-shift divisor subpower, smoothed progression count and actual pair count prove the honest 16/4 bound, while raw zero, nonzero subtraction, outside payment and the full energy remain separate',
    'CurrentChenUpsilon8TrueLiMass': 'The genuine real leading-one logarithmic-integral estimate transfers uniformly over the literal eighth product image to its same reciprocal-totient logarithmic mass, retaining its positive one-third gap; no harmonic or count mean is assumed',
    'CurrentChenUpsilon8HarmonicMean': 'The literal eighth product image is exactly its original mixed strict and weak affine prime-box test, with a genuine harmonic limit equal to the unmodified two-dimensional integral; the ordinary coefficient and adopted causal budget remain separate',
    'Part3SharedFirstFactorCharacterDictionary': 'The full shared-first-factor zero covariance has an exact nonprincipal-character expansion with both auxiliary coprime sieves and actual full-modulus principal masses; all complex factors and the second inverse first factor remain, without an analytic large-sieve payment',
    'ActualUpperPolicyFiniteBridge': 'Finite structural identities identify the same globally even-retaining policy with its literal modulus support, Mobius coefficient, physical attachment and reciprocal-totient polynomial without importing historical integral estimates',
    'SmallRoughDensityError': 'The sign-sensitive small-weight attachment has a finite nonnegative density error controlled by absolute rough mass, while the original main density retains its signed coefficient; no sharp analytic budget is assumed',
    'ActualPrimePresieveSplit': 'The actual capped target-deleted prime universe splits in its exact decreasing order at the real cutoff, and the same retained polynomial equals the fixed reciprocal-totient density with unit and squarefree endpoints retained',
    'FirstExitGenericModuli': 'Arbitrary literal first-exit policies have weight-independent fixed modulus supports and Mobius coefficients; genuine product injection retains leaf order and multiplicity before the exact signed density dictionary',
    'FirstExitOwnCubeSplice': 'The exact difference of two literal policies is reindexed at their common before-test frontier, retaining every newly admitted candidate and each original continuation instead of assuming they agree',
    'FirstExitAdmittedFrontierTuples': 'Root accepted the exact 6d68 source after strict compilation, original-object stock replay and complete type, unique inventory, safety and standard-axiom checks of all 25 actual generated declarations, with exact proper/full inputs before and after and current177 census. The original policy admitted selections have exact history and tuple permutations with multiplicities retained, finite no-repetition and exact ordinary and weighted sum identities. The sharp K arithmetic mean, original K supplier and main hLower/hUpper claims remain open.',
    'FirstExitFrontierInvariants': 'Actual retained-frontier histories recover their original mass, parity, selected labels and exact remaining smaller-prime carrier with the same target deletion, cap and strict endpoint',
    'Part3SharedFirstFactorLowConductorSW': 'The original uniform auxiliary SW family bounds one actual nonprincipal character sum at polylogarithmic conductor, retaining the full auxiliary k times delta divisor cost and uniform threshold; physical-label aggregation and the full zero-mode energy are separate',
    'Part3SharedFirstFactorLargeResidualZero': 'The literal high-conductor and large residual-tail gcd zero covariance has a universal finite Parseval and divisor-moment bound, retaining 1/Y and 1/Q1; the actual beta and gamma1 outside cost is paid by an explicit finite bound, with power/log and other regions separate',
    'Part3SharedFirstFactorSmallResidualHighConductorZero': 'The actual high-conductor and small residual-tail gcd zero covariance consumes the proved generic mean through an exact original-alpha conjugation and physical-level injection, retaining all eta powers and true divisor multiplicities; the full outside finite bound is explicit and zero assembly remains separate',
    'ActualSmallRoughAttachment': 'The same signed rough coefficient and actual small Rosser weights give a genuine physical majorant, support, unit coefficient bound and exact signed density sandwich; the absolute rough mass is used only for its explicit attachment error',
    'ActualPrimeBoxMass': 'Actual target-deleted prime tuples in the literal box have the proved positive reciprocal-totient mass limit; no box integral or selected policy mean is assumed',
    'SieveDimensionComparison': 'The actual even-center finite sieve density has exact cap-split Euler quotients and a uniform comparison with all odd primes; this finite comparison does not assert an analytic Mertens dimension estimate',
    'Part3SharedFirstFactorHighConductor': 'Arbitrary bounded complex auxiliary-coprime polynomials retain the full imprimitive character level; exact Mobius and conductor grouping plus the sharp primitive coefficient-energy theorem give the genuine uniform high-conductor mean with the first R^(1-eta) saving intact; physical-label aggregation is separate',
    'Part3SharedFirstFactorLowConductorAggregate': 'The original uniform auxiliary SW family pays the full physical first factor and both original tail labels in the actual low-conductor zero covariance, retaining tau(p*v) costs by fixed divisor moments and the genuine 1/Q1 saving; high conductor and the complete distribution remain separate',
    'ActualExtendedThirdCompactSignedDensityLimit': 'The actual signed third-policy density minus its exact initial actualPlus baseline has the original-cap residual integral limit; one legal cutoff/buffer/mesh chosen before N gives arbitrary accuracy against the original third functional, without a signed-mean premise or final K claim',
    'FinitePrimeGeometryCore': 'The extracted finite prime-sieve geometry and literal upper/lower admissibility dictionaries retain the original product, strict cube and support gates; current-source owned acceptance is separate from the older producer receipts and from analytic density limits',
    'Part3SharedFirstFactorPrimitiveUVPayment': 'The full same-p primitive U/V correction retains the original physical factor fibres and centers; actual beta and gamma1 moments are paid uniformly before atoms with a genuine arbitrary logarithmic saving, without a zero-mode or nonzero-frequency supplier',
    'Part3SharedFirstFactorZeroCovariancePayment': 'The exact complex same-p raw-zero covariance partitions all original characters into low conductor and the two high-conductor residual-gcd regions before norms; their proved estimates and original auxiliary SW pay both actual outside moments uniformly, while U/V and nonzero frequencies remain separate',
    'Part3SharedFirstFactorEnergyNonzeroReduction': 'The actual centered energy minus the complete same-p nonzero series equals the same-p zero covariance plus primitive U/V; their proved payments give a uniform energy remainder and signed squared-error reduction retaining the real part of the full nonzero sum, without assuming its estimate',
    'Part3SharedFirstFactorLargePairedGCDNonzero': 'The original large paired-gcd mask is retained identically in whole W, raw zero and the complete nonzero series; genuine tail-label grouping preserves the 1/p lcm weight, actual pair counting and both outside moments, and original geometry pays every logarithmic budget for the cleaned-alpha nonzero region',
    'CurrentChenUpsilon8OrdinaryUpperMean': 'The actual eighth finite count, positive true-li mass and genuine eighth harmonic limit combine with the same signed switched density of coefficient eight; explicit positive normalization and fixed-before-error Pan exponent give the literal ordinary eighth upper mean without a mean supplier or adopted C/K claim',
    'Part3SharedFirstFactorDifferenceReciprocity': 'The literal original shared-row CRT phase equals its constructed root, full slow phase and signed difference reciprocal phase, including zero difference and modulus one; all inverse licenses and original V Poisson-frequency transport are proved finitely, without a spectral estimate supplier',
    'Part3SharedFirstFactorLargeSupportedDeletion': 'The original asymmetric small-paired-gcd large-supported-part mask is kept identically in whole W, raw zero and full nonzero series; a genuine positive square-divisor density and same-p quotient count preserve V/p and pay both original outside moments and all three norms uniformly, leaving the small-supported spectral core separate',
    'CurrentChenUpsilon7PrimeSemiprimeSource': 'The literal seventh rough quotient is below the cube of its second prime and splits exactly into unit, prime and ordered semiprime fibres; the original central-N square-root gate, weak roughness endpoints, prime squares and full outer-pair multiplicity remain, without an arithmetic mean or C/K supplier',
    'CurrentChenUpsilon7SourceErrorBudget': 'The actual U7 unit and original P <= N^(1/5) prime and semiprime P_2 errors retain coefficient 2, ordered factors and repeated primes; their N^(19/20) bound is negligible relative to singularNormalization. The large-P main mean and full lower constant C remain open.',
    'Part3SharedFirstFactorSmallPairedSupportedReduction': 'The literal original shared-p nonzero sum splits into three exact masks; an actual finite cleaned-alpha crude bound and unit-coefficient square transfer pay both deleted pieces with the original outside moments and same-C0 auxiliary SW, leaving precisely the unchanged small paired/supported spectral core and fixed CE+3 error',
    'LogPrimeBoxIntegral': 'The literal finite-dimensional half-open prime box has a genuinely integrable reciprocal-coordinate density and exact restricted-Lebesgue product logarithm mass, including weak endpoint and zero-dimensional cases, using the fixed Mathlib Fubini theorem and preserving signed constant and terminal weights',
    'LogPrimeBoxMesh': 'The actual arbitrary finite-dimensional half-open logarithmic mesh has exact coverage, unique cell ownership and endpoint-vector convergence with one fixed step; its original boundary geometry supports real reciprocal-prime integral approximations without changing arithmetic selectors',
    'Part3LichtmanSignedDifferenceMultiplicity': 'The literal positive-f ordered signed nonzero difference multiplicity has a genuine all-positive-divisor second-moment bound with constant576, divisorMaximum fifth power and harmonic cost, retaining cross-f collisions and exact zero beyond8FHS; this is a finite multiplicity input, not spectral cancellation',
    'ActualPrimeBoxTestFunctions': 'The actual target-linked reciprocal-prime tuple sum with arbitrary signed continuous test function converges to its genuine reciprocal-coordinate Lebesgue cube integral via one fixed finite half-open mesh, exact arithmetic partitions and uniform signed error budgets; no convergence or error supplier is assumed',
    'Part3SharedFirstFactorSmallCoreFourierTruncation': 'The literal small paired supported core has an actual signed row-adaptive finite Fourier truncation with proved Schwartz tail; all original p and row label costs, complex coefficient real projection, original outside moments and fixed-before-atom unit logarithmic payment are retained, without a spectral cancellation supplier',
    'Part3SharedFirstFactorSmallCorePrimeDifferenceReindex': 'The literal compatible first-factor carrier has a genuine nonzero signed difference quotient with exact product identity, natural inverse, both signs, no-additive-term original Q1-g-D bound and injectivity; the carrier has no added prime gate, and no spectral or sum-reindex supplier is assumed',
    'CurrentChenUniformEulerNormalization': 'The actual target-prime-deleted Euler product has a genuine single threshold uniform over every fixed compact positive exponent interval and every covering cap, using exact cap identity, finite product antitonicity, two proved fixed endpoint limits and a finite compact cover; no Rosser-ratio or signed-mean supplier',
    'FirstExitValidSelection': 'Actual retained tree leaves and natural retained-modulus support are exactly constructive policy-valid chosen sublists, with both directions preserving processing order and parity; finite equivalence only, no density or distribution hypothesis',
    'Part3SharedFirstFactorSmallCoreSmoothFrequency': 'The literal original small paired supported core has a genuine smooth signed common-D frequency approximation; actual cutoff support, full complex coefficient real projection, all row labels and original outside moments are retained and its Schwartz tail pays a fixed-before-atom unit logarithmic budget, without root separation or spectral cancellation suppliers',

    'FirstExitFrontierTupleReindex': 'Actual stopped first-exit frontier histories preserve list multiplicities by an exact proper-prefix-valid sublist permutation, then genuine no-repetition permits original tuple and reciprocal-weight sum identities with target deletion, cap and strict/weak endpoints unchanged; finite dictionary only, without analytic density supplier',
    'Part3SharedFirstFactorSmallCoreSquaredFinite': 'The actual smooth core has an exact divisor-indexed signed-frequency Cauchy decomposition with complex coefficients outside the real projection; rational unsigned-slope fibres prove the resonant Gram mass nonnegative and retain the signed complementary block, with no resonance logarithmic payment or spectral cancellation supplier',
    'Part3SmoothReciprocityProfile': 'The actual complex low-pass Fourier profile with its signed positive slow reciprocity phase has genuine uniform polynomially weighted ordinary derivatives for every fixed pair of orders on Z at least one, retaining the precise degree-J modulation cost; no joint Mellin, root-operator or spectral cancellation supplier',
    'Part3SmoothReciprocityLogMixed': 'The actual signed log-monomial reciprocity weight has uniform bounds for every fixed order of mixed Frechet derivatives, with the constant preceding all varying scales and degree-j modulation cost. Quantitative Fourier L1 separation and the retained spectral bound remain open.',
    'Part3SmoothReciprocityLogFourierL1': 'Root accepted the exact current source after strict compilation, stock replay and complete type/safety/axiom checks of all 14 actual declarations. This owned Fourier L1 input does not establish full foreign-closure replay or the main C/K and hLower/hUpper claims.',
    'Part3SmoothReciprocityLogDecayJet': 'Root accepted the exact current source after strict compilation, stock replay and complete type/safety/axiom checks of all 17 actual declarations. This owned weighted reciprocity decay-jet input does not establish full foreign-closure replay or the main C/K and hLower/hUpper claims.',
    'Part3SmoothReciprocityLogFourierEnvelope': 'Root accepted the exact current source after strict compilation, stock replay and complete type/safety/axiom checks of all 17 actual declarations. This owned common Fourier envelope input does not establish full foreign-closure replay or the main C/K and hLower/hUpper claims.',
    'Part3SharedFirstFactorSupportedCoreCauchy': 'Root accepted this exact source after strict compilation, original-object stock replay and complete checks of all 13 actual generated declarations. Literal original Co support, supported complex energy and positive complete row-square Cauchy are retained; nonresonant PSD, spectral supplier and main C/K and hLower/hUpper claims remain open.',
    'Part3NonresonantManuscriptCostAlgebra': 'Root accepted this exact source after strict compilation, original-object stock replay and complete type, inventory, safety and axiom checks of all 29 actual generated declarations. It proves scalar prefactor, diagonal, spectral and zero-mode normalizations and original zero-mode payment under explicit positive geometric hypotheses. The actual spectral bound, original core C/K suppliers and nonzero 7/32 estimate remain open.',
    'Part3SmoothReciprocityLogDecayingFourierEnvelope': 'Root accepted the exact current source after strict compilation, stock replay and complete type/safety/axiom checks of all 17 actual declarations. This weighted decaying pointwise envelope preserves the common integrable kernel; the original spectral estimate and main C/K and hLower/hUpper claims remain open.',
    'Part3ResonanceOffDiagonalCount': 'The current e3acf880 projection-repair source remains uncompiled and unaccepted. The original 1a0e strict failure and source-only repair evidence remain retained. The October22 independent review falsely reported LF/CR literal and JSON defects; its R1/R2 rejection was retracted in the preserved correction checkpoint after actual AST-byte inspection, with no source repair required. Derived input preparation and corrected static review are advisory metadata, not kernel acceptance; original labels, masks, endpoints and weights are retained.',
    'CurrentChenUpsilon1011JointSource': 'Root source-reviewed the tenth/eleventh joint-source candidate with original labels, masks, endpoints and weights; it remains uncompiled and unaccepted. Its CurrentChenMeanLedger prerequisite is not owned.',
    'ActualExtendedThirdAdmittedOwnCubeBridge': 'The 123-line admitted own-cube bridge remains an uncompiled and unaccepted source candidate with original labels, masks, endpoints and weights retained. Its FirstExitAdmittedFrontierTuples prerequisite is now separately accepted for 25 actual finite selection, multiplicity and weighted-sum declarations. That prerequisite acceptance does not accept this consumer or establish the sharp K arithmetic mean, original K supplier or hUpper.',
    'CurrentChenUpsilon7LargePrimeSwitch': 'Root source-reviewed the seventh large-prime-switch candidate with original labels, masks, endpoints and weights; it remains uncompiled and unaccepted.',
    'Part3SharedFirstFactorGeneralDRootPacket': 'Root accepted the exact 183-line c165 source after strict compilation, original-object stock replay and complete type, inventory, safety and standard-axiom checks of all 3 actual generated declarations, with exact full inputs after and current176 census. Actual gcd normalization, constructed root modulus and coprimality gates, and full signed Fourier phase retain the slow factor. The nonzero spectral estimate, C/K suppliers and main hLower/hUpper claims remain open.',
    'Part3SharedFirstFactorGeneralDRowAdapter': 'Source-only complete guarded-row and original finite-block equality adapter with all four signed actual general-D phase packets and the original resonance mask retained. It remains uncompiled and unaccepted; its paired Fourier prerequisite is also unaccepted. No complementary-block positivity or spectral bound is claimed.',
    'Part3SharedFirstFactorGeneralDSupportedRowConsumer': 'Source-only 95-line cleaned supported-carrier consumer of the unchanged general-D row adapter. Original admissibility and literal supported-carrier membership discharge its positivity premises while preserving the actual cleaned atom, original scale cutoffs, signed resonance mask and complete four-branch packets. Author checkpoint 37d95e96 and independent review 2ae4bc6c record source-only review completion; kernel validation remains pending. The imported row adapter and paired Fourier prerequisite remain uncompiled and unaccepted; no complementary-block positivity, spectral bound or kernel acceptance is claimed.',
    'Part3SharedFirstFactorGeneralDPairedFourier': 'Independent source review passed for this exact source; it remains uncompiled and unaccepted. No analytic target, spectral estimate or kernel acceptance is claimed.',
    'Part3SchwartzFourierL1Sobolev': 'Genuine quantitative Fourier L1 bound in real dimension below eight, controlled by the actual normalized fourth-order operator energy with the constant chosen before all Schwartz functions. Actual-weight, decay-envelope and spectral consumers remain separate obligations.',
    'Part3SmoothReciprocityLogRegularity': 'The literal signed logarithmic reciprocity weight is genuinely smooth for all real atom parameters, its topological support lies in the fixed localizer support, and compact support follows without a smoothness premise. Quantitative Fourier L1 and spectral estimates are separate obligations.',

}
table_begin = text.index('| Module | Mathematical content | Verification |')
table_end = text.index('\n\nThese ', table_begin)
rows = []
for module in manifest['modules']:
    name = module.removeprefix('ImbalancedChen.')
    description = descriptions.get(name) or descriptions.get(name.replace('.', '/'))
    assert description, f'Missing reviewed scope description: {module}'
    count = manifest['modules'][module]['declarations']
    rows.append(f'| `{name}` | {description} | Strict compilation; original-object stock kernel replay; complete {count}-declaration types, inventory and transitive axiom audit |')
text = text[:table_begin] + '| Module | Mathematical content | Verification |\n| --- | --- | --- |\n' + '\n'.join(rows) + text[table_end:]
n, d = len(manifest['modules']), manifest['declaration_count']
count_begin = text.index('\n\nThese ', table_begin)
count_end = text.index('## Candidates that must not be counted as completed proofs', count_begin)
accepted = set(manifest['modules'])
has = lambda name: 'ImbalancedChen.' + name in accepted
scope = f'''\n\nThese {n} modules contain **{d} complete owned declarations**, including
private and generated declarations. The count is an inventory size, not
{d} independent major mathematical theorems.

'''
if has('CurrentChenOrdinaryInitialLedger') and has('CurrentChenUpsilon5OrdinaryMean'):
    scope += 'The first, second and fifth literal current count means have complete\nordinary proofs with no analytic supplier premise.\n\n'
if has('CurrentChenUpsilon6OrdinaryMean'):
    scope += '''The sixth actual ordinary count mean is also proved for E=False. Its
fixed-buffer arithmetic limit precedes the proved removal of the buffer;
the argument does not interchange these limits. It does not supply the
stronger causal h248 contribution or certify the adopted numerical L6.
The right-hand side remains the original full-rectangle sixth count;
the corrected strict inner product domain supplies a conservative lower
bound. This ordinary integral is distinct from the manuscript's adopted L6.

'''
else:
    scope += '''The accepted U6 kernel limit is an analytic integral limit on the
literal corrected rectangle. The full arithmetic ordinary count mean
still requires its own executed proof checks.

'''
if has('CurrentChenSinglePrimeUpperFiniteMean') and not has('CurrentChenUpsilon34OrdinaryUpperMean'):
    scope += '''The third and fourth actual finite upper counts now have their full
ordinary BV and centre budgets. This finite statement alone does not
provide their normalized integral upper means or adopted constants.

'''
if has('CurrentChenUpsilon34OrdinaryUpperMean'):
    scope += '''The third and fourth ordinary integral upper means are also proved
with the actual logarithmic integral normalization. This does not close
the stronger causal contributions or the complete eleven-term ledger.

'''
if has('ActualExtendedThirdFunctionalConvergence'):
    scope += '''The actual finite robust correction kernels are integrable on the
full original closed ordered domain. Their real integrals uniformly
approximate the literal unbuffered manuscript functional, with the
small-z tails and both changing boundary strips paid. This analytic
limit does not prove the same-policy arithmetic count mean.

'''
scope += 'The stronger causal contributions and the complete lower ledger remain open.\n\n'
if has('CurrentChenUpsilon9PanAggregate') and has('CurrentChenUpsilon9CoprimeGateBudget'):
    scope += '''The ninth actual zero-one product coefficient now has its bounded Pan
aggregate and its genuine signed coprimality-defect budget proved. The
Pan modulus range is the ordinary square-root range. This does not pay
the higher physical level used by the adopted policy or complete the
eleven-term lower ledger.

'''
if has('CurrentChenUpsilon9TrueLiMass') and has('CurrentChenUpsilon9SwitchedUpperDensity'):
    scope += '''The true logarithmic-integral main mass has its leading-one transport
to the same reciprocal-totient prime product mass. The actual ordinary
signed upper density has its proved normalized factor eight, with the
original rounded level and Euler normalization retained.

'''
if has('CurrentChenUpsilon9OrdinaryUpperMean'):
    scope += '''The actual ninth count now has a complete ordinary upper mean with
factor eight times its genuine two-dimensional harmonic integral. The
positive li mass and limiting integral are proved before multiplication;
no positivity assumption on the signed sieve density is used. The Pan
exponent is fixed before all error tolerances. The manuscript requires
the smaller coefficient currentK = 8452171/1250000 on the same harmonic
integral; the ordinary coefficient eight does not supply that estimate.
The stronger physical distribution level remains necessary.

'''
if has('CurrentChenUpsilon9HarmonicIntegral'):
    scope += '''The same ninth harmonic integral now has a proved moving-slice
Fubini decomposition and logarithmic antiderivative evaluation. This
identifies its exact one-dimensional manuscript expression; it does not
replay or replace a numerical integral enclosure.

'''
if has('ActualExtendedThirdCompactCellConvergence'):
    scope += '''A newly constructed compact-cell lookup recovers the same ideal
functional to every tolerance with a fixed positive third lower endpoint.
The cutoff is fixed before buffer and mesh. Removal of an entire cell
is paid by the actual full tail at cutoff plus mesh width. This compares
nonnegative integral kernels; identification and the arithmetic mean of
the new signed policy remain separate.

'''
if has('Part3TransposedDispersion'):
    scope += '''The original signed dispersion error has an exact transpose placing
the actual SW coefficient on the paired side. The other coefficient's
genuine divisor second moment, new smoothing scale and Poisson phases
are retained. This identity does not itself supply the zero-mode or
nonzero-frequency bounds needed by strong physical distribution.

'''
if has('Part3TransposedZeroCovariance'):
    scope += '''The actual transposed raw zero mode minus its literal primitive main
term is now identified with the complete grouped coprime covariance.
The original auxiliary SW family pays that covariance, retaining all
factor labels, the tau-three fibre bound and original beta L2 logarithms.
The literal U/V residuals and nonzero frequencies are separate proof steps,
accepted only where listed with their own executed checks.

'''
if has('ActualExtendedThirdCompactPrimeHarmonic'):
    scope += '''The actual finite prime-box harmonic sums also converge to the same
compact cell functional. Their pointwise strict/weak affine sandwich
retains prime atoms on ownership and ordering walls. Cutoff, buffer and
finite mesh are chosen before the arithmetic target, recovering the
original ideal to every tolerance. The signed first-exit arithmetic
density and original policy identification remain separate.

'''
if has('CurrentChenUpsilon8ProductPan'):
    scope += '''The literal eighth prime-or-unit source now has its genuine zero-one
product coefficient, rounded two-thirds Pan window and true-li bounded
aggregate majorant. This is a finite source and distribution step; the
original unit and small-prime losses, signed sieve errors and full eighth
ordinary mean each require the separate executed checks listed below.

'''
if has('CurrentChenUpsilon8SourceErrorBudget'):
    scope += '''The literal eighth count has an exact large-prime, small-prime and
unit-fibre partition. Genuine source injectivity gives power bounds for
both discarded parts and a zero singular-normalized error limit. The full
eighth ordinary upper mean is a separate assembly and harmonic step.

'''
if has('CurrentChenUpsilon8CoprimeGateBudget'):
    scope += '''The actual eighth non-coprime main-term gate is paid with both
genuine prime factors and the reciprocal-totient divisor estimate, without
assuming coprimality of the remaining cofactor. The original signed upper
Rosser coefficient is retained. Its negligible-error threshold precedes
every cap, level and selected positive-modulus set through N; this does
not supply the eighth leading mean or a density constant.

'''
if has('CurrentChenUpsilon8FiniteMean'):
    scope += '''The literal eighth count is now bounded by its actual li main mass
times the same complete signed upper density, plus every positive multiple
of the original singular normalization. The genuine Pan exponent is fixed
before the tolerance, and the arithmetic threshold precedes every cap.
All four Pan, gate, small-prime and unit errors are paid internally. The
leading-one li transport and actual eighth harmonic limit have their own
exact-source acceptance below. Neither provides the adopted causal density.

'''
if has('CurrentChenUpsilon8TrueLiMass'):
    scope += '''The literal eighth true-li main mass has a uniform leading-one
transport to its same original reciprocal-totient logarithmic mass, with
the genuine one-third gap retained. This is a main-mass comparison, without
an assumed arithmetic count mean or a changed sieve coefficient.

'''
if has('CurrentChenUpsilon8HarmonicMean'):
    scope += '''The actual eighth logarithmic reciprocal-totient mass now converges
to its original two-dimensional harmonic integral. The mixed strict/weak
affine walls are retained pointwise on the arithmetic prime boxes; a
continuous clamp equals the original kernel on that exact region. Its
ordinary factor-eight density route still cannot supply the smaller
adopted causal row budget or currentK. This component does not assert the
complete eighth arithmetic count mean.

'''
if has('Part3SharedFirstFactorDispersion'):
    scope += '''A separate, genuine joint Cauchy in the original beta and first
physical factor keeps that same factor p on both squared-row labels. The
full primitive p carrier, same-C0 auxiliary SW family, original V cutoff,
signed residue, full lcm and every integer Poisson frequency are literal.
The outside factor has the honest extra Q1; the new summed centered energy
must be bounded at scale V U^2 / Q1. Old independent-first-factor zero/U/V,
gcd-region and reciprocal estimates do not automatically pay this energy.
In particular gcd(p v1,p v2)=p gcd(v1,v2), so the old small full-gcd region
cannot simply be transferred to a residual-gcd partition. Slow phases,
the new energy and the complete restricted medium bound remain open.

'''
if has('Part3SharedFirstFactorPairCount'):
    scope += '''Actual ordered pairs retain their unit gates and common congruence
for every positive first factor, including composites. Gcd cancellation,
a finite inverse-square telescope and the harmonic moment bound the full
large-paired-gcd pair count, including its diagonal. Its analytic consumers
are accepted individually below.

'''
if has('Part3SharedFirstFactorLargePairedGCDW'):
    scope += '''The actual cleaned-alpha whole W under its original large-paired-gcd
mask has the proved bound C X^epsilon (4 V/Q1 + 1) times
(16 U^2/Y + 4 Q1 U (1 + log(2 U))). The same first factor, complete primitive
carrier, complex coefficients and signed residue remain. This pays that
masked whole W only: raw-zero subtraction, outside-factor payment, the
remaining regions and the full centered energy are separate obligations.

'''
if has('Part3SharedFirstFactorCharacterDictionary'):
    scope += '''The full actual shared-factor zero covariance has an exact
nonprincipal-character expansion. Both auxiliary coprime sieves, the
full-modulus principal masses, complex conjugates and coefficient
V/(p L phi(p D)) remain. This finite dictionary supplies no conductor
large-sieve bound or completed zero-mode payment.

'''
if has('Part3SharedFirstFactorLowConductorSW'):
    scope += '''At polylogarithmic conductor, the original uniform auxiliary SW
family bounds one actual nonprincipal character sum with its constants
chosen before the atom, auxiliary level and character. Lowering the
conductor keeps every nonunit in k*delta, so the true divisor penalty is
tau(k*delta)^C0, or tau(p*v)^C0 at the actual shared-factor specialization.
The full physical low-conductor aggregate and generic high-conductor mean
have their separate acceptance records below; their residual consumers
and complete zero-mode assembly remain separate.

'''
if has('ActualExtendedThirdInitialCutoff'):
    scope += '''The initial dyadic-first-stop polynomial is exactly the actual
ordinary plus density at its literal floor-grid prime cutoff. Zero cutoff
exponents, strict endpoints, cap N and all old-level tests are retained.
An asymptotic bound must still be proved before replacing that cutoff by
rho through genuine parameter limits.

'''
if has('Part3PairedAlphaDeletion'):
    scope += '''Deleting actual original-alpha divisors of the moving signed residue
has a proved finite error and every logarithmic payment, with the same
auxiliary-SW constants preserved. The cleaned atom retains the original
beta and physical factor labels. Its full nonzero-frequency estimate
still needs the remaining region proofs.

'''
if has('ActualExtendedThirdCompactResidualProfile'):
    scope += '''The actual old-minus-cell lower Rosser densities with original cap N
now converge to the same retained-cell harmonic functional. An auxiliary
larger cap is restored exactly on each actual atom; failed strict own-cube
gates are paid pointwise, including equality. This is a genuine density
limit; the full signed policy splice and counting error remain separate.

'''
if has('Part3TransposedDifferenceMoment'):
    scope += '''The entire same-mask large-physical-gcd nonzero Fourier contribution
is paid after original beta L2. Actual diagonal and off-diagonal divisor
moments supply the whole-W bound, and same-mask raw zero is also paid.
The both-small region, its reciprocal and slow phases, and the full
restricted medium estimate remain open.

'''
if has('ActualExtendedThirdDistinctProductHarmonic'):
    scope += '''Strictly ordered actual prime triples are now injective under their
original product by unique factorization. The finite sum is transported
exactly to that product image with its full reciprocal-totient weight and
the same recovered triple test. Its harmonic limit is the same original
functional, with all fixed cutoffs preceding N. No new factorial is
inserted and the signed first-exit counting dictionary remains separate.

'''
if has('ActualPrimeMultiLabelNormalization'):
    scope += '''The literal full-product Mobius coefficient pays repeated-prime
diagonals before each original same-label factorial is cancelled once.
The multi-label identity retains complete block-product vectors. Further
identification with the original ordered policy carrier is still needed.

'''
if has('Part3TransposedLargeGCDFourier'):
    scope += '''The actual paired large-gcd Fourier remainder is paid after the
original beta L2 factor, including the same-mask raw-zero subtraction and
the signed-residue cleanup. This covers that gcd region only; the other
regions and the full physical distribution endpoint remain open.

'''
if has('Part3TransposedPrimitiveVPayment'):
    scope += '''Both literal primitive-center residuals U-P0 and V-P0 are paid after
the actual original beta L2 factor, with every requested real logarithmic
decay. The honest V estimate keeps two alpha masses and the full physical
cap; original medium geometry pays them. Nonzero frequencies and the
complete physical distribution endpoint remain open.

'''
if has('Part3SharedFirstFactorHighConductor'):
    scope += '''The full generic high-conductor mean is proved for arbitrary bounded
complex coefficients, with the original auxiliary coprime mask and full
imprimitive character level. Exact Mobius/conductor regrouping and the
sharp primitive coefficient energy retain Q N^2/R^(1-eta) without a global
Q^eta loss in that term. The constant precedes all varying parameters.
The actual physical tail-label aggregation is a separate consumer.

'''
if has('Part3SharedFirstFactorLowConductorAggregate'):
    scope += '''The low-conductor zero covariance is now bounded after summing the
full physical first factor and both original ordered tail labels. The
original auxiliary SW family supplies the estimate, with the full
tau(p*v) cost paid by fixed divisor moments and the genuine 1/Q1 saving.
This is low conductor on every residual gcd, not the full zero estimate.

'''
if has('FirstExitOwnCubeSplice'):
    scope += '''The next-selection enumeration uses an explicit List.rec implementation
with unconditional nil/cons equations. Its complete new generated census
passes the unchanged safety audit. The former unsafe-helper INCOMPLETE
attempt remains archived and is not retrospectively accepted.

'''
if has('CurrentChenUpsilon8OrdinaryUpperMean'):
    scope += '''The actual eighth arithmetic count now has its ordinary upper mean
with coefficient eight and the unchanged eighth harmonic integral. This does
not supply the adopted causal constant K.

'''
if has('Part3SharedFirstFactorZeroCovariancePayment'):
    scope += '''Under the original uniform auxiliary SW input, the full same-p
zero covariance is now assembled from low-conductor and both high-conductor
residual regions, with both original outside moments paid. The primitive
U/V correction has its separate completed payment.

'''
if has('Part3SharedFirstFactorEnergyNonzeroReduction'):
    scope += '''The literal centered energy minus the complete same-p nonzero
series is the zero covariance plus the primitive U/V correction. Its proved
payment reduces the signed squared error to the real part of that same
nonzero series; no estimate of the remaining series is assumed.

'''
if has('Part3SharedFirstFactorDifferenceReciprocity'):
    scope += '''The actual shared-row CRT phase has an exact root, slow and signed
reciprocal-phase factorization with all inverse licenses constructed from
the original tuple. Zero difference, modulus one, signed frequencies and
the original V/L Poisson scale are retained. This identity is not a spectral
estimate.

'''
if has('Part3SharedFirstFactorLargePairedGCDNonzero'):
    scope += '''The original large paired-gcd nonzero contribution now has every
requested logarithmic saving after both actual outside moments. Whole W,
raw zero and the complete nonzero series keep exactly the same mask.

'''
if has('Part3SharedFirstFactorLargeSupportedDeletion'):
    scope += '''The small-paired-gcd, large-supported-part region is also paid
uniformly, using a positive square-divisor density and the genuine same-p
quotient-block count. Its original asymmetric mask, true V/p denominator,
both outside moments and all three W/zero/nonzero norms are retained. The
small-supported reciprocal/spectral core remains open.

'''
if has('CurrentChenUpsilon7PrimeSemiprimeSource'):
    scope += '''The actual seventh quotient is strictly below the cube of its
second prime. Its full count splits exactly into unit, prime and ordered
two-prime fibres, retaining central-N square-root walls, weak endpoints,
prime squares and outer-label multiplicity. No seventh analytic mean or
full eleven-row lower bound follows from this finite partition alone.

'''
if has('Part3SharedFirstFactorSmallPairedSupportedReduction'):
    scope += '''The literal complete nonzero series is now partitioned into all
three paired/supported masks. A proved cleaned-alpha size bound and squared
error transfer leave coefficient one on the actual small core, with fixed
CE+3 logarithmic error under the original uniform auxiliary SW input. No
spectral estimate for this core is a hypothesis of the reduction.

'''
if has('ActualExtendedThirdInitialCutoff'):
    scope += '''The actual initial-cutoff selector equals the ordinary upper
Rosser polynomial at its literal floored cutoff, including cutoff zero.
The complete finite modulus support and squarefree Mobius/totient dictionary
are proved; the corresponding original-policy signed mean is still open.

'''
if has('LogPrimeBoxIntegral') and has('LogPrimeBoxMesh'):
    scope += '''The actual reciprocal-coordinate density has its exact product
logarithm Lebesgue integral, including signed weights and zero dimension.
The original half-open mesh has exact coverage, disjoint cells, unique
boundary ownership and endpoint-vector convergence. These are genuine
integral inputs, separate from arithmetic mean and signed-policy estimates.

'''
if has('ActualPrimeBoxTestFunctions'):
    scope += '''The genuine target-linked reciprocal-prime tuple sum now converges
for every signed continuous cube test to its reciprocal-coordinate Lebesgue
integral. One finite uniform mesh is fixed before the arithmetic limit;
the actual positive masses pay both signed approximation errors. This is
an arithmetic integral limit, without an assumed convergence supplier.

'''
if has('Part3SharedFirstFactorSmallCoreFourierTruncation'):
    scope += '''The literal small core has a proved finite Fourier truncation.
Its row-dependent ceiling keeps the original physical lcm, both frequency
signs and real projection inside the complex coefficient. A genuine Schwartz
tail pays every original carrier and outside moment with a fixed-before-atom
unit logarithmic budget. Cancellation within the finite window remains open.

'''
if has('Part3SharedFirstFactorSmallCorePrimeDifferenceReindex'):
    scope += '''On the original compatible first-factor carrier the signed
quotient is nonzero, has both exact sign identities and recovers the first
factor injectively. Its bound retains Q1, the row gcd and the tail gcd with
no additive term. No primeness gate is added to the actual carrier. This
arithmetic license does not yet supply a spectral sum estimate.

'''
if has('Part3LichtmanSignedDifferenceMultiplicity'):
    scope += '''The literal ordered positive-f signed nonzero difference
multiplicity has a genuine finite second moment with constant576, the fifth
power of the divisor maximum and explicit harmonic cost, for every positive
auxiliary divisor. Cross-f collisions and exact zero above8FHS are retained.
This does not establish cancellation in the actual physical spectral core.

'''
scope += '''The shared-first-factor primitive U/V and zero-covariance
aggregations preserve both original outside moments and the actual p sum.
The remaining small-core spectral bound, original-policy mean constants
and final unconditional arithmetic lower/upper inputs are still open.

'''
text = text[:count_begin] + scope + text[count_end:]
begin = text.index('## Candidates that must not be counted as completed proofs')
end = text.index('## External work reused', begin)
section = f'''## Candidates that must not be counted as completed proofs

The {len(candidates['candidates'])} unaccepted source candidates are listed with exact source
hashes in `verification/proof-continuation/2026-10-15/unaccepted-candidates.json`.
They are excluded from the accepted module/declaration inventory above.
Original failed attempts remain failures; replacement sources need their own checks.

'''
for module, entry in candidates['candidates'].items():
    section += f"* `{module.removeprefix('ImbalancedChen.')}`: {entry['note']}\n"
section += '''
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

'''
text = text[:begin] + section + text[end:]
text = text.replace('All approved compiler/checker processes had terminated at this checkpoint.', 'The compiler/checker owner serializes all heavy work through slot zero;\nsource and proof work continue independently between those jobs.')
text = text.replace('1. Compile and replay the actual U5 mean chain, resolving its old import\n   resource obstruction without changing the required analytic statement.', '1. Complete the remaining actual ordinary/causal lower means with their\n   genuine row coefficients and physical remainder budgets.')
path.write_text(text, encoding='utf-8', newline='\n')
print(json.dumps({'modules': n, 'declarations': d, 'candidates': len(candidates['candidates'])}))
