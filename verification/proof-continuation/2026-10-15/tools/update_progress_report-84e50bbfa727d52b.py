from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'
manifest = json.loads((DEST / 'manifest.json').read_text(encoding='utf-8'))
candidates = json.loads((DEST / 'unaccepted-candidates.json').read_text(encoding='utf-8'))
path = ROOT / 'docs/PROOF_CONTINUATION_2026-10-15.md'
text = path.read_text(encoding='utf-8')
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
ninth mean and the lower ledger.

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
