"""Archive successful owned proof evidence without upgrading its scope.

This copies existing terminal receipts byte for byte. It does not run Lean,
repair a receipt, accept a cache, or claim an aggregate proof.
"""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'
MODULES = [
    'ImbalancedChen.CurrentChenPairLevelGeometry',
    'ImbalancedChen.CurrentChenPairRosser',
    'ImbalancedChen.CurrentChenUpsilon6KernelBuffer',
    'ImbalancedChen.CurrentChenUpsilon6OrdinarySieveKernel',
    'ImbalancedChen.Part3CenteredFourier',
    'ImbalancedChen.Certificates.PairedV2FullBuchstab',
    'ImbalancedChen.CurrentChenPairDensity',
    'ImbalancedChen.CurrentChenPairHarmonicMean',
    'ImbalancedChen.CurrentChenUpsilon5OrdinaryMean',
    'ImbalancedChen.CurrentChenPairMovingHarmonic',
    'ImbalancedChen.CurrentChenUpsilon5FiniteMean',
    'ImbalancedChen.Part3ComplexDispersion',
    'ImbalancedChen.ActualSieveGapTailDecay',
    'ImbalancedChen.ActualSieveGapTailBounds',
    'ImbalancedChen.ActualThirdPrefixTailIntegral',
    'ImbalancedChen.ActualThirdPrefixTailIntegralCore',
    'ImbalancedChen.CurrentChenRosserEndpointDictionary',
    'ImbalancedChen.CurrentChenRosserLowerRectangle',
    'ImbalancedChen.CurrentChenFixedEulerNormalization',
    'ImbalancedChen.Part3ComplexCRTConsumer',
    'ImbalancedChen.Part3ComplexCRTFiniteFourier',
    'ImbalancedChen.ActualExtendedThirdIdealCap',
    'ImbalancedChen.ActualExtendedThirdOrderedIntegral',
    'ImbalancedChen.ActualExtendedThirdClosedIntegral',
    'ImbalancedChen.CurrentChenInitialRosserRemainder',
    'ImbalancedChen.CurrentChenOrdinaryInitialMean',
    'ImbalancedChen.CurrentChenOrdinaryInitialLedger',
    'ImbalancedChen.CurrentChenUpsilon6FiniteMean',
    'ImbalancedChen.CurrentChenUpsilon6OrdinarySource',
    'ImbalancedChen.Part3CommonSmoothCutoff',
    'ImbalancedChen.ActualExtendedThirdPhysicalCell',
    'ImbalancedChen.ActualExtendedThirdDyadicCoverage',
    'ImbalancedChen.Part3CommonPoisson',
    'ImbalancedChen.CurrentChenUpsilon6OrdinaryMean',
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

]
MODULES = [m for m in MODULES if (ROOT / (m.replace('.', '/') + '.lean')).is_file()]


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def copy(source, dest):
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        assert sha(source) == sha(dest), f'Existing evidence differs: {dest}'
    else:
        shutil.copyfile(source, dest)
    assert sha(source) == sha(dest)


def main():
    subprocess.run(['git', 'merge-base', '--is-ancestor',
                    '3c51704ff4da3abc94cd06e39e62ee2a1bc4f6af', 'HEAD'],
                   cwd=ROOT, check=True)
    assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == \
        'codex/proof-continuation-20261015', 'Unexpected publication branch'
    frozen = {m: sha(ROOT / (m.replace('.', '/') + '.lean')) for m in MODULES}
    previous = json.loads((DEST / 'manifest.json').read_text(encoding='utf-8')) \
        if (DEST / 'manifest.json').exists() else {'modules': {}}
    for module, record in previous['modules'].items():
        assert frozen.get(module) == record['source_sha256'], \
            'Previously accepted source changed or disappeared: ' + module
    audits = []
    accepted = {}
    for receipt in sorted((STATE / 'audits').glob('*/receipt.json')):
        r = json.loads(receipt.read_text())
        if r.get('status') != 'PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS':
            continue
        if not r['targets'] or any(frozen.get(m) != h for m, h in r['targets'].items()):
            continue
        assert r['inputs_before'] == r['inputs_after']
        assert not r['external_closure_replay_claimed'] and not r['unconditional_main_claimed']
        for m, h in r['targets'].items():
            accepted[m] = {'source_sha256': h, 'declarations': r['declaration_counts'][m],
                           'audit': (Path('audits') / receipt.parent.name / 'receipt.json').as_posix(),
                           'audited_object_parts': r['inputs_before']['owned_object_parts'][m],
                           'audited_pins': r['inputs_before']['pins'],
                           'audited_lean_real_sha256': r['inputs_before']['lean_real_sha256']}
        audits.append(receipt.parent)
    assert len(accepted) >= 4, 'Rosser and the first three leaves must have complete audits'
    assert all(m in accepted for m in MODULES[:4])
    assert previous['modules'].keys() <= accepted.keys(), 'Accepted module inventory regressed'
    # Read immutable terminal-run receipts once; preserve the same per-module
    # eligibility assertions and lexicographically latest receipt selection.
    strict_runs = [(receipt, json.loads(receipt.read_text()))
                   for receipt in (STATE / 'runs').glob('*/receipt.json')]
    for module, record in accepted.items():
        options = []
        for receipt, r in strict_runs:
            if r.get('module') == module and r.get('status') == 'PASS' and \
                    r.get('binding', {}).get('source_sha256') == record['source_sha256']:
                assert r['binding'] == r['binding_after']
                options.append((receipt, r))
        assert options, 'No successful actual source compile: ' + module
        receipt, r = sorted(options, key=lambda item: item[0])[-1]
        assert r['warnings_as_errors'] and r['exit_code'] == 0
        assert r['object_parts'] == record['audited_object_parts'], 'Compile/replay objects differ: ' + module
        assert r['binding']['pins'] == record['audited_pins']
        assert r['binding']['lean_real_sha256'] == record['audited_lean_real_sha256']
        record['compile'] = (Path('compilation') / receipt.parent.name / 'receipt.json').as_posix()
        record['object_parts'] = r['object_parts']
        for name in ('receipt.json', 'stdout.log'):
            copy(receipt.parent / name, DEST / 'compilation' / receipt.parent.name / name)
    for directory in audits:
        for file in directory.iterdir():
            if file.is_file():
                copy(file, DEST / 'audits' / directory.name / file.name)
    for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        copy(ROOT / name, DEST / 'pins' / name)
    for file in (STATE / 'runtime.py', STATE / 'runtime.before-6144-budget.py',
                 STATE / 'audit_owned.py', STATE / 'export_candidates.py', Path(__file__),
                 STATE / 'update_progress_report.py', STATE / 'check_checkpoint.py',
                 ROOT / 'verification/parts/p0/queue/AuditTemplate.lean',
                 ROOT.parent / 'goldbach-integration/verification/parts/takeover-p0/checker_memory_guard.py'):
        copy(file, DEST / 'tools' / (file.stem + '-' + sha(file)[:16] + file.suffix))
    metadata = {
        'scope': 'Advisory source/header census and independent source review only; not a recorded-object closure or a Lean proof check',
        'runtime_v1_plain_import_limitation': True,
        'inherited_cache_promoted': False,
        'compressed_originals': [],
    }
    census_sources = sorted(STATE.glob('import-walker-v2-census*.json'))
    census_sources.extend(sorted((STATE / 'source-reviews').glob('*/*.json')))
    census_sources.extend(source for source in sorted((STATE / 'source-reviews').glob('*.json'))
                          if source.stat().st_size > 1024 * 1024)
    if (STATE / 'initial-remainder-import-diff.json').is_file():
        census_sources.append(STATE / 'initial-remainder-import-diff.json')
    for source in census_sources:
        original_hash = sha(source)
        target = DEST / 'metadata' / (source.stem + '-' + original_hash[:16] + '.json.gz')
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            with source.open('rb') as src, target.open('wb') as dst:
                with gzip.GzipFile(filename='', mode='wb', fileobj=dst, mtime=0) as zipped:
                    shutil.copyfileobj(src, zipped)
        with gzip.open(target, 'rb') as unzipped:
            assert hashlib.file_digest(unzipped, 'sha256').hexdigest() == original_hash
        assert sha(source) == original_hash
        metadata['compressed_originals'].append({
            'original_name': source.name, 'original_sha256': original_hash,
            'original_relative_path': source.relative_to(STATE).as_posix(),
            'original_bytes': source.stat().st_size,
            'archive': target.relative_to(DEST).as_posix(),
            'compressed_sha256': sha(target),
        })
    for source in sorted(STATE.glob('import_walker_v2.*.py')):
        copy(source, DEST / 'tools' / source.name)
    for source in sorted((STATE / 'source-reviews').glob('*/*.py')):
        copy(source, DEST / 'tools' / (source.stem + '-' + sha(source)[:16] + source.suffix))
    review = STATE / 'u5-source-review.json'
    if review.exists():
        copy(review, DEST / 'metadata' / ('u5-source-review-' + sha(review)[:16] + '.json'))
    for source in (STATE / 'tail_import_dag.json', STATE / 'tail_split.json',
                   ROOT / '.lake/lower-proof-analysis/finite-import-diff.json'):
        if source.is_file():
            copy(source, DEST / 'metadata' / (source.stem + '-' + sha(source)[:16] + source.suffix))
    for source in sorted((STATE / 'source-reviews').glob('*.json')):
        if source.stat().st_size <= 1024 * 1024:
            copy(source, DEST / 'metadata' / (source.stem + '-' + sha(source)[:16] + source.suffix))
    for source in (ROOT / '.lake/lower-proof-analysis/density-initial-model-dag.json',):
        if source.is_file():
            copy(source, DEST / 'metadata' / (source.stem + '-' + sha(source)[:16] + source.suffix))
    (DEST / 'metadata/census-scope.json').write_text(json.dumps(metadata, indent=2) + '\n', newline='\n')
    for module, record in accepted.items():
        assert sha(ROOT / (module.replace('.', '/') + '.lean')) == record['source_sha256']
    files = {str(file.relative_to(DEST)).replace('\\', '/'): sha(file)
             for file in sorted(DEST.rglob('*')) if file.is_file() and file.name != 'manifest.json'}
    manifest = {
        'schema': 'proof-continuation-owned-evidence-v1',
        'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'baseline': '3c51704ff4da3abc94cd06e39e62ee2a1bc4f6af',
        'manuscript': 'ba6ec11d800eccc54406490631895e174de85766',
        'scope': 'Strict actual source compilation, owned original-object stock replay, complete owned types/inventory/transitive axioms only',
        'main_theorem_proved': False,
        'aggregate_build_claimed': False,
        'external_closure_replay_claimed': False,
        'modules': accepted,
        'declaration_count': sum(r['declarations'] for r in accepted.values()),
        'files': files,
        'notes': [
            'Producer receipts/logs are copied byte for byte; compressed census originals recover exactly by SHA256; no old receipt was rewritten.',
            'Absolute paths in receipts are historical execution paths, not portable commands.',
            'Archived runtime versions may not include every earlier producer version; receipt hashes remain authoritative.',
            'Inherited remote-cache prerequisites remain development-only; this archive does not claim their independent replay.',
            'An integrity check of this manifest is not a Lean proof check.',
        ],
    }
    (DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', newline='\n')
    print(json.dumps({'modules': list(accepted), 'declarations': manifest['declaration_count'],
                      'files': len(files), 'path': str(DEST)}, indent=2), flush=True)


if __name__ == '__main__':
    main()
