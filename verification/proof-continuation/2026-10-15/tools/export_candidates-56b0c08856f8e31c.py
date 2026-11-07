"""Record unaccepted source candidates separately from verified components."""
from pathlib import Path
import hashlib
import json
import shutil

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'

CANDIDATES = {
    'ImbalancedChen.Part3ElementaryE1RealEndpoint': 'Root applied exact source 5c386ee17594c075b81b15d56143284fd0f77364f87129d0a96632f17064f8ad with 11 written proofs and two definitions for real-endpoint finite interval E1 payment. It remains uncompiled and unaccepted. Its exact source chain and all hypotheses are retained; no complete analytic E1, M2, spectral or main theorem is claimed.',
    'ImbalancedChen.Part3ShiftedTauFiniteInterval': 'Root applied exact source 3a2c777a96f2758a4ced96f8f78881d88f28e7f2bb011dc82b2d5223a3d3f298 with nine written proofs and two definitions. It preserves the original positive v<=floor(6*x) carrier, deletes v=a before the absolute shift, retains full nonnegative kappa and the exact finite 2*K interval payment. It remains uncompiled and unaccepted; no capped-kappa, Big-O, M2, spectrum, 7/32 or main-theorem estimate is claimed.',
    'ImbalancedChen.Part3CommonPM2FiniteFold': 'Root applied exact source eda9f3c56d44e87fb9cfa17c5420900c58d871d53acf9db5a9236464c333bc32 with ten definitions and nine written proofs. Its finite labelled common-p M2 divisor fold imports the now root-accepted exact CommonP geometry parent; original smoothing, labels, signed deletion and outside energy are retained. The fold source itself remains uncompiled and unaccepted; the analytic M2 supplier, spectrum, 7/32 and main theorem remain OPEN.',
    'ImbalancedChen.Part3WeightedRefinedSignedDifference': 'The current exact source 6e16d77482cd63d5aef89ff62b90f2ca95c30e5cf0828800c20dcc49373aabff has one current-source proper PASS and actual ONE readonly classifier PASS (generic178 inputs); it remains uncompiled and unaccepted, with the original f26985 failure chain preserved. It proves only the M-squared times original-576 weighted energy bound and exact nu endpoint. No packet embedding, c-class spectral supplier, kernel acceptance or main theorem is claimed.',
    'ImbalancedChen.CurrentChenPairDensity': 'The replacement actual initial-sieve supplier route is source-reviewed; only a matching successful strict compile and complete owned audit can accept it.',
    'ImbalancedChen.CurrentChenUpsilon5OrdinaryMean': 'The actual ordinary U5 mean remains a source candidate until its exact density source and final count consumer pass execution and owned audit.',
    'ImbalancedChen.CurrentChenUpsilon6OrdinaryMean': 'The full ordinary unmasked mean argument is present as source, including finite payment and fixed-buffer passage; exact-source execution and complete owned audit remain required.',
    'ImbalancedChen.Part3ReciprocalAPSupplier': 'New target not executed; limited external prerequisite bootstrap stopped at a resource failure.',
    'ImbalancedChen.Certificates.PairedV2FullCertificate': 'Not executed; requires the full original-strip chain, beyond the frozen baseline pilot.',
    'ImbalancedChen.ActualThirdPrefixTailIntegral': 'Broad arithmetic tuple/profile bridge is not compiled; the separate canonical integral core is verified.',
    'ImbalancedChen.Part3SharedFirstFactorGeneralDRowAdapter': 'The current exact 249-line source 33974efcc178c95b2f965e673451e8762c65a057bf0c192f4abae542bddf09e5 retains all 11 written declaration headers, the original guarded-row and finite-block equality adapter, all four signed general-D phase packets and the resonance mask. Its current-source ONE proper and ONE v2 readonly classifier passed. The original 8fbd strict failure and complete failure chain remain preserved; the repaired 3397 source remains uncompiled and unaccepted. Its Paired Fourier parent is already owned and accepted. No complementary-block positivity, spectral bound or main theorem is claimed.',
    'ImbalancedChen.Part3SharedFirstFactorGeneralDSupportedRowConsumer': 'Source-only 95-line cleaned supported-carrier consumer of the unchanged general-D row adapter. Original admissibility and literal supported-carrier membership discharge its positivity premises while preserving the actual cleaned atom, original scale cutoffs, signed resonance mask and complete four-branch packets. Author checkpoint 37d95e96 and independent review 2ae4bc6c record source-only review completion; kernel validation remains pending. The imported row adapter remains uncompiled and unowned, while its Paired Fourier prerequisite is already owned and accepted. No complementary-block positivity, spectral bound or kernel acceptance is claimed.',
    'ImbalancedChen.Part3ResonanceOffDiagonalCount': 'The current exact c0a0c6130bf0406c24bacae440806b514c144075bc9e623cadd0687554bab8d2 source has one current-source proper PASS and actual ONE readonly classifier PASS (fullwrapper174/generic178); it remains uncompiled and unaccepted. Original strict failures remain preserved. No spectral/kernel or main-theorem acceptance is claimed.',
}
for _module in (
    'ImbalancedChen.CurrentChenRosserEndpointDictionary',
    'ImbalancedChen.CurrentChenRosserLowerRectangle',
    'ImbalancedChen.CurrentChenFixedEulerNormalization',
    'ImbalancedChen.Part3ComplexCRTConsumer',
    'ImbalancedChen.Part3ComplexCRTFiniteFourier',
    'ImbalancedChen.Part3CommonSmoothCutoff',
    'ImbalancedChen.Part3CommonPoisson',
    'ImbalancedChen.ActualExtendedThirdIdealCap',
    'ImbalancedChen.ActualExtendedThirdOrderedIntegral',
    'ImbalancedChen.ActualExtendedThirdClosedIntegral',
    'ImbalancedChen.ActualExtendedThirdPhysicalCell',
    'ImbalancedChen.ActualExtendedThirdDyadicCoverage',
    'ImbalancedChen.CurrentChenInitialRosserRemainder',
    'ImbalancedChen.CurrentChenOrdinaryInitialMean',
    'ImbalancedChen.CurrentChenOrdinaryInitialLedger',
    'ImbalancedChen.CurrentChenUpsilon6OrdinarySource',
    'ImbalancedChen.CurrentChenUpsilon6FiniteMean',
    'ImbalancedChen.CurrentChenRosserUpperEndpointDictionary',
    'ImbalancedChen.CurrentChenRosserUpperRectangle',
    'ImbalancedChen.CurrentChenQuotientUpperRosser',
    'ImbalancedChen.CurrentChenSinglePrimeUpperFiniteMean',
    'ImbalancedChen.Part3RealComponentReduction',
    'ImbalancedChen.Part3FactorFiberDivisor',
    'ImbalancedChen.ActualExtendedThirdFirstCubeMargin',
    'ImbalancedChen.ActualExtendedThirdGammaApproximation',
    'ImbalancedChen.ActualExtendedThirdLowerFactorRegularity',
    'ImbalancedChen.CurrentChenSinglePrimeUpperDensity',
    'ImbalancedChen.CurrentChenTrueLiNormalization',
    'ImbalancedChen.Part3CanonicalReciprocalData',
    'ImbalancedChen.ActualExtendedThirdFinitePhysicalKernel',
    'ImbalancedChen.ActualExtendedThirdStripIntegral',
    'ImbalancedChen.CurrentChenSinglePrimeHarmonicMean',
    'ImbalancedChen.CurrentChenUpsilon34OrdinaryUpperMean',
    'ImbalancedChen.Part3CanonicalReciprocalPhase',
    'ImbalancedChen.ActualExtendedThirdFiniteTailIntegral',
    'ImbalancedChen.ActualExtendedThirdBoundaryLoss',
    'ImbalancedChen.ActualExtendedThirdLeastWinningIndex',
    'ImbalancedChen.ActualExtendedThirdActionParameters',
    'ImbalancedChen.ActualExtendedThirdWholeCellActions',
    'ImbalancedChen.ActualTwoCapacityGreedy',
    'ImbalancedChen.Part3CleanBetaLargeGCDMajorant',
    'ImbalancedChen.Part3PolynomialResidueDivisorBound',
    'ImbalancedChen.CurrentChenUpsilon9PrimeSource',
    'ImbalancedChen.CurrentChenUpsilon9UnitBudget',
    'ImbalancedChen.ActualExtendedThirdCompactKernelApproximation',
    'ImbalancedChen.ActualExtendedThirdKernelL1Convergence',
    'ImbalancedChen.ActualDwellSelectedRemainder',
    'ImbalancedChen.ActualSelectedSubproductParameters',
    'ImbalancedChen.CurrentChenUpsilon9ProductCoefficient',
    'ImbalancedChen.Part3ActualLargeGCDBetaMass',
    'ImbalancedChen.ActualExtendedThirdFunctionalConvergence',
    'ImbalancedChen.CurrentChenUpsilon9CoprimeGateBudget',
    'ImbalancedChen.ActualTwoFactorRepairMonomials',
    'ImbalancedChen.ActualSelectedPairFactorization',
    'ImbalancedChen.Part3SignedDivisorDeletion',
    'ImbalancedChen.CurrentChenUpsilon9PanAggregate',
    'ImbalancedChen.ActualExtendedThirdFiniteCellIntegral',
    'ImbalancedChen.Part3TransposedDispersion',
    'ImbalancedChen.Part3PairedUpperEndpointSW',
    'ImbalancedChen.ActualPrimeTupleNormalization',
    'ImbalancedChen.ActualFrozenCapacitySlots',
    'ImbalancedChen.ActualRoughVectorEndpointBudget',
    'ImbalancedChen.CurrentChenUpsilon9FiniteMean',
    'ImbalancedChen.ActualFrozenSelectedPairSlots',
    'ImbalancedChen.CurrentChenUpsilon9TrueLiMass',
    'ImbalancedChen.ActualExtendedThirdCompactCellCutoff',
    'ImbalancedChen.ActualExtendedThirdCompactCellConvergence',
    'ImbalancedChen.ActualFrozenSlotCoefficientRegrouping',
    'ImbalancedChen.CurrentChenUpsilon9HarmonicMean',
    'ImbalancedChen.CurrentChenUpsilon9SwitchedUpperDensity',
    'ImbalancedChen.ActualFrozenSelectedPairAssignment',
    'ImbalancedChen.ActualPrimeSlotSquarefreeSymmetry',
    'ImbalancedChen.ActualPrimeIcoCellTestFunctions',
    'ImbalancedChen.Part3TransposedZeroCovariance',
    'ImbalancedChen.Part3SmoothProgressionError',
    'ImbalancedChen.Part3SmoothCoprimeError',
    'ImbalancedChen.ActualExtendedThirdCompactHarmonicProfile',
    'ImbalancedChen.ActualExtendedThirdCompactPrimeHarmonic',
    'ImbalancedChen.Part3PrimitiveZeroReal',
    'ImbalancedChen.Part3TransposedPrimitiveU',
    'ImbalancedChen.Part3TransposedPrimitiveUMoment',
    'ImbalancedChen.Part3TransposedPrimitiveUPayment',
    'ImbalancedChen.Part3TransposedPrimitiveV',
    'ImbalancedChen.Part3TransposedPrimitiveVMoment',
    'ImbalancedChen.Part3TransposedPrimitiveVPayment',
    'ImbalancedChen.Part3PairedAlphaDeletion',
    'ImbalancedChen.CurrentChenUpsilon9OrdinaryUpperMean',
    'ImbalancedChen.CurrentChenUpsilon9HarmonicSlices',
    'ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral',
    'ImbalancedChen.Part3TransposedZeroPayment',
    'ImbalancedChen.Part3TransposedZeroUVPayment',
    'ImbalancedChen.Part3TransposedGCDPoissonMask',
    'ImbalancedChen.ActualExtendedThirdOwnedLabelOrder',
    'ImbalancedChen.ActualExtendedThirdDistinctPrimeHarmonic',
    'ImbalancedChen.ActualExtendedThirdDistinctProductHarmonic',
    'ImbalancedChen.CurrentChenUpsilon8PrimeSource',
    'ImbalancedChen.CurrentChenUpsilon8ProductPan',
    'ImbalancedChen.ActualPrimeMultiLabelNormalization',
    'ImbalancedChen.Part3TransposedLargeGCDFourier',
    'ImbalancedChen.ActualExtendedThirdCompactResidualProfile',
    'ImbalancedChen.ActualPrimeDisjointLabelProducts',
    'ImbalancedChen.ActualPrimeFineLabelSortedSelector',
    'ImbalancedChen.ActualPrimeFineWordMultiplicity',
    'ImbalancedChen.ActualPrimeFineWordSlotRegrouping',
    'ImbalancedChen.Part3TransposedModulusGCDZero',
    'ImbalancedChen.ActualRosserOddBox',
    'ImbalancedChen.ActualPrimeBoxEulerLower',
    'ImbalancedChen.ActualRosserEvenBox',
    'ImbalancedChen.Part3TransposedModulusProgression',
    'ImbalancedChen.Part3TransposedDifferenceMoment',
    'ImbalancedChen.ActualExtendedThirdCompactUpperRho',
    'ImbalancedChen.ActualExtendedThirdCompactFrontier',
    'ImbalancedChen.FiniteUpperCarrierCore',
    'ImbalancedChen.ActualExtendedThirdCompactPolicySaving',
    'ImbalancedChen.Part3SharedFirstFactorDispersion',
    'ImbalancedChen.Part3TransposedCanonicalReciprocalPhase',
    'ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget',
    'ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget',
    'ImbalancedChen.ActualExtendedThirdInitialCutoff',
    'ImbalancedChen.Part3SharedFirstFactorPairCount',
    'ImbalancedChen.CurrentChenUpsilon8FiniteMean',
    'ImbalancedChen.Part3SharedFirstFactorLargePairedGCDW',
    'ImbalancedChen.CurrentChenUpsilon8TrueLiMass',
    'ImbalancedChen.CurrentChenUpsilon8HarmonicMean',
    'ImbalancedChen.Part3SharedFirstFactorCharacterDictionary',
    'ImbalancedChen.ActualUpperPolicyFiniteBridge',
    'ImbalancedChen.SmallRoughDensityError',
    'ImbalancedChen.ActualPrimePresieveSplit',
    'ImbalancedChen.FirstExitGenericModuli',
    'ImbalancedChen.FirstExitOwnCubeSplice',
    'ImbalancedChen.FirstExitFrontierInvariants',
    'ImbalancedChen.Part3SharedFirstFactorLowConductorSW',
    'ImbalancedChen.Part3SharedFirstFactorLargeResidualZero',
    'ImbalancedChen.Part3SharedFirstFactorSmallResidualHighConductorZero',
    'ImbalancedChen.ActualSmallRoughAttachment',
    'ImbalancedChen.ActualPrimeBoxMass',
    'ImbalancedChen.SieveDimensionComparison',
    'ImbalancedChen.Part3SharedFirstFactorHighConductor',
    'ImbalancedChen.Part3SharedFirstFactorLowConductorAggregate',
    'ImbalancedChen.ActualExtendedThirdCompactSignedDensityLimit',
    'ImbalancedChen.FinitePrimeGeometryCore',
    'ImbalancedChen.Part3SharedFirstFactorPrimitiveUVPayment',
    'ImbalancedChen.Part3SharedFirstFactorZeroCovariancePayment',
    'ImbalancedChen.Part3SharedFirstFactorEnergyNonzeroReduction',
    'ImbalancedChen.Part3SharedFirstFactorLargePairedGCDNonzero',
    'ImbalancedChen.CurrentChenUpsilon8OrdinaryUpperMean',
    'ImbalancedChen.Part3SharedFirstFactorDifferenceReciprocity',
    'ImbalancedChen.Part3SharedFirstFactorLargeSupportedDeletion',
    'ImbalancedChen.CurrentChenUpsilon7PrimeSemiprimeSource',
    'ImbalancedChen.CurrentChenUpsilon7SourceErrorBudget',
    'ImbalancedChen.Part3SharedFirstFactorSmallPairedSupportedReduction',
    'ImbalancedChen.LogPrimeBoxIntegral',
    'ImbalancedChen.LogPrimeBoxMesh',
    'ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity',
    'ImbalancedChen.ActualPrimeBoxTestFunctions',
    'ImbalancedChen.Part3SharedFirstFactorSmallCoreFourierTruncation',
    'ImbalancedChen.Part3SharedFirstFactorSmallCorePrimeDifferenceReindex',
    'ImbalancedChen.CurrentChenUniformEulerNormalization',
    'ImbalancedChen.FirstExitValidSelection',
    'ImbalancedChen.Part3SharedFirstFactorSmallCoreSmoothFrequency',
    'ImbalancedChen.FirstExitFrontierTupleReindex',
    'ImbalancedChen.Part3SharedFirstFactorSmallCoreSquaredFinite',
    'ImbalancedChen.Part3SmoothReciprocityProfile',
    'ImbalancedChen.Part3SmoothReciprocityLogMixed',
    'ImbalancedChen.Part3SmoothReciprocityLogRegularity',
    'ImbalancedChen.Part3SchwartzFourierL1Sobolev',
    'ImbalancedChen.Part3SmoothReciprocityLogFourierL1',
    'ImbalancedChen.CurrentChenUpsilon1011JointSource',

):
    if (ROOT / (_module.replace('.', '/') + '.lean')).is_file():
        CANDIDATES[_module] = (
            'Root accepted this exact Fourier L1 source after strict compilation, stock replay and complete checks of all 14 actual declarations; full foreign-closure replay and the main C/K and hLower/hUpper claims remain open.'
            if _module == 'ImbalancedChen.Part3SmoothReciprocityLogFourierL1'
            else 'Source candidate only until exact-source strict compilation and complete owned replay/type/axiom evidence are accepted; no full main theorem is asserted.')


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    verified = json.loads((DEST / 'manifest.json').read_text())['modules']
    rows = {}
    for module, note in CANDIDATES.items():
        if module in verified:
            continue
        path = ROOT / (module.replace('.', '/') + '.lean')
        digest = sha(path)
        assert module not in verified, 'Accepted proof unexpectedly appears in candidate-only list'
        rows[module] = {'status': 'UNACCEPTED_SOURCE', 'source_sha256': digest, 'note': note}
    failures = []
    for receipt in sorted((STATE / 'runs').glob('*/receipt.json')):
        r = json.loads(receipt.read_text())
        module = r.get('module')
        if module not in rows and module not in verified:
            continue
        if r.get('status') not in ('FAILED', 'RESOURCE_STOP', 'GUARD_ERROR'):
            continue
        target = DEST / 'unaccepted-attempts' / receipt.parent.name
        target.mkdir(parents=True, exist_ok=True)
        for name in ('receipt.json', 'stdout.log'):
            src = receipt.parent / name
            dst = target / name
            if dst.exists():
                assert sha(src) == sha(dst)
            else:
                shutil.copyfile(src, dst)
        failures.append({
            'module': module, 'status': r['status'],
            'attempt_source_sha256': r['binding']['source_sha256'],
            'matches_current_candidate': module in rows and r['binding']['source_sha256'] == rows[module]['source_sha256'],
            'module_now_has_a_verified_new_source': module in verified,
            'receipt': (target.relative_to(DEST) / 'receipt.json').as_posix(),
        })
    report = {
        'schema': 'unaccepted-candidates-v1',
        'scope': 'Source preservation and original failed-attempt evidence; no proof acceptance',
        'main_theorem_proved': False,
        'candidates': rows,
        'failed_attempts': failures,
    }
    target = DEST / 'unaccepted-candidates.json'
    target.write_text(json.dumps(report, indent=2) + '\n', newline='\n')
    print(json.dumps({'candidate_modules': len(rows), 'failed_attempts': len(failures)}), flush=True)


if __name__ == '__main__':
    main()
