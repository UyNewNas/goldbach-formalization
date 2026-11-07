"""Record unaccepted source candidates separately from verified components."""
from pathlib import Path
import hashlib
import json
import shutil

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'

CANDIDATES = {
    'ImbalancedChen.Part3ShiftedTauFiniteInterval': 'Root applied exact repaired source 5be137eef6bcf78b29fc29188e9158fd2f15b577eca7d72be6671c750ebceb82 with nine written proofs and two definitions. Its first current-source strict attempt failed only at sum_image inference; strict1, stock0 and retry0. Terminal source-reviews/20261022-shifted5be137-current187-operator-terminal-HOLD.json SHA256 188c3aec723132e83f2d575e1fcdae0f8c2af91199389e9da8a897294bcb209b, original failed receipt SHA256 5bab8c325de596ce153487ed1be3256bbeae62d0d1a34fbedd852344e3e6b920 and complete compiler log remain preserved. The earlier 2ed54 source failed with seven API/type errors; its original terminal a4b637482cea7e611ee3761dfe9e70d473016b99a1501cda00106e1ae0fa945c and receipt f3c7be0dddad472639fb8feaeac32ab7ba09af296475ecc1b3fdce81d779dc74 remain history. The independently reviewed d006 repair remains a draft, not applied or kernel accepted. The original positive v<=floor(6*x) carrier, deletion of v=a before the absolute shift, full nonnegative kappa and exact finite 2*K interval payment remain. No analytic M2, spectral, 7/32 or main-theorem estimate is claimed.',
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
    'ImbalancedChen.Part3LiteralPrincipalEnergySupplier': 'The current exact source 2f814fc1fe97565c8e1e67db05c503312b6f33892dc68486041cf274585aa402 is source-reviewed only (independent review SHA256 c9e83403f3690debf68cb859c31498f5190181e90806ce2e4821caf5172b1dce). ONE current-source proper PASS was followed by the first capture FAIL at collect line50, KeyError ImbalancedChen.ActualGridEnvelopes; classifier, strict and stock were not executed, with zero retries. FIRSTFAIL/HOLD summary source-reviews/20261022-principal2f81-current189-ONE-readonly-preparation-FIRSTFAIL-HOLD.json SHA256 b837949a1519a23a75bb12ac0dfd2ca516b6871008f0d0d787d96619c20c2e4f records 75 project parents:28 owned and47 unowned against union189. The complete missing-parent topology rounds/20261022-EU2f81-missing-owned47-topological-readonly-inventory.json SHA256 385f158450d5ae95b128810d4051ba239e408a85ec845b6add7f84be4f354122 preserves all47 dependency gaps. Existing exact caches are not owned-audit acceptance; the all-parent-owned check must not be weakened. This is an ownership/admission dependency frontier, not a confirmed manuscript mathematical gap. Target actual declaration count is unknown, with no kernel acceptance. The finite original principal-energy supplier source does not establish analytic M2, retained variance, nonzero spectrum, 7/32, sharp C/K or the main theorem.',
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
