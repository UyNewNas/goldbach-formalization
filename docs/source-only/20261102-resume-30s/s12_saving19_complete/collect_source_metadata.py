"""Read source bytes/text and JSON metadata only; no proof or numerical evaluation."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = ROOT.parent

def entry(path, role):
    p = Path(path)
    if not p.is_absolute():
        p = ROOT / p
    raw = p.read_bytes()
    text = raw.decode('utf-8-sig')
    lines = text.splitlines()
    namespaces = re.findall(r'^namespace\s+(\S+)', text, re.M)
    namespace = namespaces[0] if namespaces else None
    out = {
        'path': str(p.relative_to(ROOT)).replace('\\', '/') if p.is_relative_to(ROOT) else str(p).replace('\\', '/'),
        'absolute_path': str(p).replace('\\', '/'),
        'role': role,
        'raw_sha256': hashlib.sha256(raw).hexdigest(),
        'bytes': len(raw), 'lines': len(lines),
    }
    if p.suffix == '.lean':
        out.update(module='ImbalancedChen.' + p.stem,
            namespace=namespace,
            intended_install_target='ImbalancedChen/' + p.name,
            direct_imports=re.findall(r'^import\s+(\S+)', text, re.M),
            declarations=[{'name': (namespace + '.' if namespace else '') + m.group(2),
                           'kind': m.group(1), 'line': i}
                for i, line in enumerate(lines, 1)
                if (m := re.match(r'^(?:private\s+)?(theorem|def|abbrev|structure)\s+(\S+)', line))])
    return out

new_sources = [entry(p, 'new strict source; uncompiled') for p in sorted(HERE.glob('*.lean'))]
reuse_paths = [
 ('ImbalancedChen/OriginalAscendingNineteenArithmeticResidual.lean', 'existing uniform actual ordinary residual supplier; reused rather than duplicated'),
 ('ImbalancedChen/P2OriginalThirdMinorantLogDictionary.lean', 'original pair licence, 3/256 margin, true-third minorant, current density comparison'),
 ('ImbalancedChen/OriginalAscendingThirteenCellOwnership.lean', 'actual13 StrictRows, source ownership and original isolated sixth-parent action'),
 ('ImbalancedChen/OriginalAscendingThirteenLiteralAffineRows.lean', 'exact original97 strict affine rows'),
 ('ImbalancedChen/OriginalAscendingThirteenExportOwnershipJoin.lean', 'original literal/semantic/source dictionary'),
 ('docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalFourteenThirteenCurrentSource.lean', 'R06 actual13-after14 List and full continuation preservation'),
 ('docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean', 'concrete original bank/data and actual fourteen policy'),
 ('docs/source-only/20261102-resume-30j/saving19_geometry/P4AOriginalSaving19CommonHistory.lean', 'existing common originalSeed/lambda3 history supplier'),
 ('docs/source-only/20261102-resume-30j/saving19_geometry/P2OriginalSaving19HistoricalMinorant.lean', 'actual rational pair minorant and source historyMargin'),
 ('docs/source-only/20261102-resume-30j/saving19_floor/P2OriginalSaving19SourceMeasure.lean', 'original source hull, integrability and selectedSaving'),
 ('docs/source-only/20261102-resume-30k/saving19_preservation/P4AOriginalSaving19BankExhaustion.lean', 'existing original13 mesh exhaustion'),
 ('docs/source-only/20261102-resume-30k/saving19_preservation/P2OriginalSaving19BankIntegral.lean', 'existing bank integral convergence; not a prime mean'),
 ('docs/source-only/20261102-resume-30k/saving19_preservation/P4AOriginalSaving19BankFrontier.lean', 'actual selected bank/source dictionary'),
 ('docs/source-only/20261028-resume-30g/upper_chronology/P4AOriginalLive171819PrimeBank.lean', 'concrete current-parent/source/support dictionary'),
 ('docs/source-only/20261028-resume-30g/upper_chronology/P4AOriginalLive171819CommonParent.lean', 'actual held sixth bound by original chosen-plane envelope'),
 ('docs/source-only/20261028-resume-30g/upper_chronology/P4AOriginalLive171819Atlas.lean', 'original source rows and chronology source labels'),
 ('docs/source-only/20261102-resume-30m/saving19_owned_integral/P2OriginalSaving19OwnedIntegral.lean', 'existing no-argument original13/28918 Q96 endpoint; not repeated'),
 ('docs/source-only/20261102-resume-30p/saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean', 'required effective same-module repair inherited through M/K'),
 ('docs/source-only/20261102-resume-30o/all22_common_history/P4AOriginalCommonArchiveSchedule.lean', 'fixedSchedule chi=e/20'),
 ('docs/source-only/20261102-resume-30o/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean', 'actual original fourth/fifth source inputs'),
 ('docs/source-only/20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedConstructor.lean', 'held current policy6; not full adopted sixth'),
 ('docs/source-only/20261102-resume-30q/saving19_instance/REGISTRY.json', 'inherited complete M endpoint dependency/source evidence'),
 ('docs/source-only/20261102-resume-30q/saving19_instance/REPORT.md', 'exact existing endpoint audit'),
 ('docs/source-only/20261102-resume-30q/reviews/q24_review_saving_geometry.md', 'independent original13/28918 source review'),
 ('docs/source-only/20261102-resume-30r/all22_actual_sources/REPORT.md', 'R06 final original source/current-parent scope'),
 ('docs/source-only/20261102-resume-30r/all22_actual_sources/REGISTRY.json', 'R06 frozen pins and declarations'),
 ('docs/source-only/20261102-resume-30r/reviews/r26_review_reserves_density.md', 'independent R06 source and mean boundary'),
 ('lean-toolchain', 'pinned toolchain text'),
 ('lake-manifest.json', 'pinned dependency revisions'),
]
reused = [entry(p, role) for p, role in reuse_paths]
originals = [entry(BASE / p, role) for p, role in [
 ('chen-imbalanced-semiprimes/paper/source/manuscript-body.tex', 'original current policy, arithmetic residual, density/compiler paragraph'),
 ('chen-imbalanced-semiprimes/proof-library/source/eighth-third-minorant-analytic-review-20261009.tex', 'exact original13 selected-family licence/history/residual/separation paragraphs'),
 ('goldbach-research/eighth-third-minorant-extension-20261009-exact.py', 'original selected A23/s23_low adapter read as text only'),
 ('goldbach-research/eighth-third-minorant-extension-20261009-family-exact.py', 'original13 selection with initial cell4 once; text only'),
 ('goldbach-research/eighth-third-moment-refinement-20261009.py', 'original factor/moment adapter read as text only'),
 ('1_+_1.748_lean_proofs/main.md', 'read-only authoritative yellow-node scope'),
]]

def walk(x):
    if isinstance(x, dict):
        yield x
        for y in x.values():
            yield from walk(y)
    elif isinstance(x, list):
        for y in x:
            yield from walk(y)

k_registry_path = ROOT / 'docs/source-only/20261102-resume-30k/saving19_preservation/REGISTRY.json'
k_registry = json.loads(k_registry_path.read_text(encoding='utf-8-sig'))
mathlib = next(x for x in walk(k_registry)
    if x.get('module') == 'Mathlib.MeasureTheory.Integral.DominatedConvergence' and 'path' in x)
module_map = {x['module']: x for x in new_sources + reused if 'module' in x}
module_map['Mathlib.MeasureTheory.Integral.DominatedConvergence'] = {
    **mathlib, 'pin_status': 'inherited exact K API-source record; no new WSL read; remote pinned dependency is authoritative'}
direct = []
for source in new_sources:
    for imp in source['direct_imports']:
        target = module_map[imp]
        direct.append({'from': source['module'], 'import': imp,
            'source': {k: v for k, v in target.items() if k in
                ('path', 'absolute_path', 'raw_sha256', 'sha256', 'bytes', 'module', 'pin_status')}})

registry = {
    'schema_version': 1, 'batch': '20261102-resume-30s', 'task': 's12_saving19_complete',
    'owner': '/root/s12_saving19_complete', 'yellow_node': 'P2.6',
    'whole_assigned_yellow_scope_source_complete': False,
    'status': 'SOURCE_ONLY_PARTIAL_ACTUAL_SUPPLIERS_WHOLE_ARITHMETIC_MEAN_OPEN',
    'compiled': False, 'kernel_verified': False, 'formal_credit': 0,
    'inherited_finite_bodies': 'UNEVALUATED', 'new_axioms': 0,
    'target_arithmetic_mean_assumed': False, 'original_parent_licence_assumed': False,
    'whole_node_target_premises_eliminated': 0,
    'constants': {'c': '49044063/25000000', 'K': '8452171/1250000',
        'saving19_q96': '283388722705335806564439/2^96', 'cutoff': '53/13824',
        'root_cutoff': '19/96', 'selected_mask': 138, 'density_coefficient': 4,
        'new_cap_buffer': '1/1000000'},
    'pins': {'lean': 'leanprover/lean4:v4.33.0-rc1',
        'mathlib': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
        'native': '09b97db5764ade1246bfb77206baa1b124760958',
        'public_parent': 'e2a05f73d5f169fff847d72dcfcc66ec54ad4f87'},
    'new_sources': new_sources, 'direct_import_resolution': direct,
    'reused_sources_and_reviews': reused, 'original_sources': originals,
    'inherited_mathlib_api_source_record': mathlib,
    'new_locally_discharged_premises': [
        'actual original13 bank source/current-parent licence after14, including H7',
        'unspecified compact source and assumed small real trim loss in common history',
        'assumed localized after14 continuation and preservation outside13/prior14'],
    'remaining_mathematical_obligations': [
        'prime tuple admission on a single paid inner-source schedule',
        'complete reciprocal occurrence error payment and genuine original13 prime integral mean',
        'ordinary integrated endpoint for actual localized same-policy change',
        'positive-presieve endpoint by projecting whole new tree with paid budget',
        'actual full sixth and full87 chronological binding including intervening17/18',
        'All22 and final separate density/compiler reserves'],
    'same_policy_scope': 'concrete R06 fourteen -> localized original13 with held actual6; not full87',
    'review': {'agent': '/root/s26_review_policy_savings',
        'status': 'narrow mathematical static scope checked by messages; final reviewer artifact owned by S26',
        'compiler_or_kernel_acceptance': False},
    'remote_targets': [s['module'] for s in new_sources],
    'required_axiom_targets': [
        'ImbalancedChen.P4AOriginalThirteenLocalizedContinuation.physical_sub_previous_eq_source',
        'ImbalancedChen.P4AOriginalThirteenLocalizedContinuation.original_fourteen_continuation_preserved',
        'ImbalancedChen.P2OriginalThirteenUniformArithmeticResidual.exists_original_bank_residual_error',
        'ImbalancedChen.P2OriginalThirteenPaidCommonHistory.exists_paid_original_history',
        'ImbalancedChen.P2OriginalSaving19OwnedIntegral.original_endpoint_le_selectedSaving'],
    'effective_source_override': {'module': 'ImbalancedChen.P2Winner9ActualEightSimplexMoment',
        'path': 'docs/source-only/20261102-resume-30p/saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean',
        'reason': 'inherited required same-name forward integral_const_mul repair'},
    'report': entry(HERE / 'REPORT.md', 'strict scope and remaining premises'),
    'metadata_script': entry(Path(__file__), 'bytes/text/JSON metadata only'),
    'verification_boundary': 'no local build, Lean/Lake/compiler, guard, numerical evaluation/replay, Git/CI mutation, child agent or usage query',
}
(HERE / 'REGISTRY.json').write_text(json.dumps(registry, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
for p in sorted(HERE.glob('*.lean')) + [HERE / 'REPORT.md', HERE / 'REGISTRY.json']:
    print(p.name, hashlib.sha256(p.read_bytes()).hexdigest())
