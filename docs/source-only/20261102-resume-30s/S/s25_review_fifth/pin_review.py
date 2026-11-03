"""Metadata only: read source text/bytes and write this review's pins.
No Lean, guard, numerical producer, mathematical data evaluation, or replay.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
BASE = ROOT / 'docs/source-only/20261102-resume-30s'
OUT = BASE / 'S/s25_review_fifth'
SLOTS = [
    's03_parent_jensen_geometry', 's04_parent_jensen_integral',
    's05_taylor_weighted_hessian', 's06_five_dim_midpoint',
    's07_stored_old_archive_binding', 's08_full_fifth_floor',
]
PRIMARY = {
    SLOTS[0]: ['P5OriginalParentJensenGeometry', 'P5OriginalParentJensenArchiveGeometry'],
    SLOTS[1]: ['P5OriginalParentBoxJensen', 'P5OriginalParentJensenIntegral'],
    SLOTS[2]: ['P5OriginalTaylorWeightedAxisCalculus', 'P5OriginalTaylorWeightedHessian'],
    SLOTS[3]: ['P5OriginalTaylorFiveDimensionalMidpoint', 'P5OriginalTaylorSameBoxGeometry', 'P5OriginalTaylorActualMidpointIntegral'],
    SLOTS[4]: ['P5OriginalTaylorRationalData', 'P5OriginalStoredOldArchiveBinding'],
    SLOTS[5]: ['P5OriginalParentSameReserveTransport', 'P5OriginalFullFifthFloorIntegral', 'P5OriginalStoredFifthEndpoint', 'P5RecordedOldFifthBlockTotals'],
}
def pin(path):
    path = Path(path)
    data = path.read_bytes()
    result = {'absolute_path': path.as_posix(), 'bytes': len(data),
              'raw_sha256': hashlib.sha256(data).hexdigest()}
    if path.suffix == '.lean':
        text = data.decode('utf-8-sig')
        namespace = re.search(r'^namespace\s+(\S+)', text, re.M)
        ns = namespace.group(1) if namespace else ''
        result['intended_module'] = 'ImbalancedChen.' + path.stem
        result['direct_imports'] = [
            {'line': n, 'module': match.group(1)}
            for n, line in enumerate(text.splitlines(), 1)
            if (match := re.match(r'^import\s+(\S+)', line))]
        result['declarations'] = [
            {'line': n, 'kind': match.group(1), 'name': (ns + '.' if ns else '') + match.group(2)}
            for n, line in enumerate(text.splitlines(), 1)
            if (match := re.match(r'^(?:private\s+)?(?:noncomputable\s+)?(theorem|def|abbrev|structure)\s+(\S+)', line))]
        result['compiled'] = False
        result['kernel_verified'] = False
    return result

source_pins = []
author_pins = []
for slot in SLOTS:
    folder = BASE / slot
    if not folder.exists():
        folder = BASE / 'S' / slot
    source_pins.extend(pin(folder / (name + '.lean')) for name in PRIMARY[slot])
    author_pins.extend(pin(p) for name in ('REPORT.md', 'REGISTRY.json')
                       if (p := folder / name).exists())

anchors = [
    BASE / 'BRIEF.md',
    ROOT / 'docs/source-only/20261102-resume-30r/reviews/r25_review_archive_history.md',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_old_defect/REPORT.md',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_old_defect/REGISTRY.json',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_reserve64/REPORT.md',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_reserve64/REGISTRY.json',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_reserve64/P5HistoricalActualReserve64Budget.lean',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_reserve64/P5HistoricalActualReserve64Schedule.lean',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalParentJensenRawFields.lean',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalTaylorAffineBranchBinding.lean',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalTaylorActualSignedKernel.lean',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalTaylorWeightDerivatives.lean',
    ROOT / 'docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalTaylorAffineRatioDerivatives.lean',
    ROOT / 'docs/source-only/20261102-resume-30q/fifth_parent/P1HistoricalFifthFullOriginalFloorEnvelope.lean',
    ROOT / 'docs/source-only/20261028-resume-30b/upper_fifth/P5NamedFifthPayloadSemantics.lean',
    ROOT / 'docs/source-only/20261028-resume-30e/upper_fifth/P5OriginalChildIntegerWireBinding.lean',
    ROOT / 'docs/source-only/20261028-resume-30/upper_jensen/P5OldFifthFirstFConcavity.lean',
    ROOT / 'docs/source-only/20261028-paper-first/cohort03/upper/sources/81adeddb234aa886fbe26ba36f0b1183de9ba632734c0ce7a7b9cf5dab336640/20261028-Upper-Sol6-Phase3-RecordedBlockTotals.lean.txt',
]
original = [ROOT.parent / 'chen-imbalanced-semiprimes/paper/source/manuscript-body.tex']
original += [ROOT.parent / 'goldbach-research' / name for name in (
    'certify_fifth_prefix_jensen.py', 'certify_fifth_prefix_adaptive.py',
    'certify_fifth_prefix_taylor_pilot.py', 'certify_fifth_prefix_taylor_full.py',
    'certify_fifth_prefix_subdivision.py', 'fifth-prefix-taylor-pilot.tex',
    'fifth-prefix-taylor-full.tex', 'fifth-prefix-subdivision-refinement.tex')]

text_checks = {}
geo = (BASE / SLOTS[0] / 'P5OriginalParentJensenArchiveGeometry.lean').read_text(encoding='utf-8-sig')
geo_ids = re.findall(r'^theorem block(\d{3})_original_parent_geometry\s*:', geo, re.M)
text_checks['geometry_declared_block_ids'] = geo_ids
text_checks['geometry_exact_declared_000_to_142'] = geo_ids == [f'{i:03d}' for i in range(143)]
stored_path = BASE / SLOTS[4] / 'P5OriginalStoredOldArchiveBinding.lean'
if stored_path.exists():
    stored = stored_path.read_text(encoding='utf-8-sig')
    blocks = re.findall(r'theorem block(\d{3})_stored_old_binding\s*:(.*?)(?=\nset_option|\ntheorem all_original)', stored, re.S)
    maps = []
    for bid, body in blocks:
        raw_ids = re.findall(r'P1HistoricalFifthSavedDataBlock(\d{3})\.rows', body)
        saved_ids = re.findall(r'P5SubdivisionStoredBlock(\d{3})\.rows', body)
        i = int(bid)
        expected_raw = [f'{2*i:03d}', f'{2*i+1:03d}'] if i < 71 else ['142']
        maps.append({'block': bid, 'typed_source_blocks': raw_ids, 'stored_source_blocks': saved_ids,
                     'text_position_map_matches': raw_ids == expected_raw and saved_ids == [bid]})
    text_checks['stored_block_mapping'] = maps
    text_checks['stored_exact_declared_000_to_071'] = [b for b, _ in blocks] == [f'{i:03d}' for i in range(72)]

terminal_specs = {
    'P5OriginalFullFifthFloorIntegral': [
        'original_stored_old_floor_le_parentIntegral', 'each_original_stored_floor_sub_reserve',
        'full_original_stored_floor_sub_reserve', 'original_fifth_endpoint_sub_reserve',
        'exists_original_fifth_safe_integral'],
    'P5OriginalStoredFifthEndpoint': ['original_stored_fifth_endpoint'],
    'P5OriginalStoredOldArchiveBinding': ['original_stored_old_eq_max'],
    'P5OriginalTaylorActualMidpointIntegral': ['original_taylorLowerQ_le_signedIntegral'],
}
terminals = []
for module, names in terminal_specs.items():
    source = next(p for p in source_pins if p['intended_module'] == 'ImbalancedChen.' + module)
    content = Path(source['absolute_path']).read_text(encoding='utf-8-sig')
    for name in names:
        match = re.search(r'^theorem\s+' + re.escape(name) + r'\b(.*?)\s*:=', content, re.M | re.S)
        if not match:
            raise ValueError('Missing terminal type: ' + module + '.' + name)
        terminals.append({'name': 'ImbalancedChen.' + module + '.' + name,
                          'absolute_path': source['absolute_path'], 'source_sha256': source['raw_sha256'],
                          'line': content[:match.start()].count('\n') + 1,
                          'exact_source_type': match.group(0)[:-2].rstrip()})

summary_source = anchors[-1].read_bytes()
summary_materialized = (BASE / SLOTS[5] / 'P5RecordedOldFifthBlockTotals.lean').read_bytes()
text_checks['recorded_summary_exact_except_two_Inhabited_derivations'] = (
    summary_source.replace(b'deriving DecidableEq, Repr', b'deriving DecidableEq, Repr, Inhabited') == summary_materialized)
endpoint_text = (BASE / SLOTS[5] / 'P5OriginalStoredFifthEndpoint.lean').read_text(encoding='utf-8-sig')
endpoint_blocks = re.findall(r'^theorem stored_block(\d{3})_new_sum\s*:', endpoint_text, re.M)
text_checks['endpoint_exact_declared_000_to_071'] = endpoint_blocks == [f'{i:03d}' for i in range(72)]

registry = {
    'task': 'S25 independent original fifth-floor / P1.4 review',
    'status': 'FINAL_PRIMARY_SOURCE_REVIEW',
    'reviewer_owned_scope': OUT.as_posix(),
    'compiled': False, 'kernel_verified': False, 'formal_credit': 0, 'green': False,
    'finite_mathematical_bodies': 'UNEVALUATED',
    'whole_original_fifth_yellow_source_complete': True,
    'whole_P1_4_source_complete': False,
    'scope': 'Original yellow27 actual typed/literal per-parent floor to total fifth integral; broader raw stored-output authentication and full87 current-policy scope remain P1.4 obligations.',
    'optional_S07_raw_NPY_excluded': True,
    'target_equivalent_fields_or_terminal_premises_found': False,
    'new_axioms_or_sorry_admit_found_in_reviewed_source': False,
    'actual_terminal_types': terminals,
    'reviewed_live_S_sources': source_pins,
    'author_report_registry_pins': author_pins,
    'original_source_pins': [pin(p) for p in original],
    'frozen_and_reused_anchor_pins': [pin(p) for p in anchors],
    'text_only_checks': text_checks,
    'remote_requirements': {
        'toolchain': 'leanprover/lean4:v4.33.0-rc1',
        'mathlib': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
        'native_upstream': 'subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958',
        'same_source_success_seen': False,
        'full_terminal': 'ImbalancedChen.P5OriginalFullFifthFloorIntegral.exists_original_fifth_safe_integral',
        'full_parent_terminal': 'ImbalancedChen.P5OriginalFullFifthFloorIntegral.full_original_stored_floor_sub_reserve',
        'evidence': ['published commit/tree and exact recursive import manifest',
                     'all actual analytic/data/finite dependencies elaborate on pinned toolchain',
                     'exact theorem type shows no target-equivalent licence input',
                     'print axioms of actual full terminal; no sorryAx/new axiom/unsafe substitute',
                     'reliable run conclusion, logs, artifact hashes bound to reviewed bytes'],
    },
    'report': pin(OUT / 'REPORT.md'),
    'remaining_formal_gaps': ['exact import staging/elaboration', 'all inherited and new finite bodies UNEVALUATED', 'same-source remote kernel and axiom evidence'],
    'remaining_assigned_yellow27_mathematical_premises': [],
    'possible_substantive_manuscript_gap_evidence': None,
    'operations': {'local_lean_lake_compiler': False, 'proof_guard': False,
                   'mathematical_producer_replay': False, 'git_ci_mutation': False,
                   'author_edit': False, 'child_agents': False, 'quota_inspection': False},
}
(OUT / 'REGISTRY.json').write_text(json.dumps(registry, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps({'sources': len(source_pins), 'metadata_files': len(author_pins),
                  'geometry_block_text_coverage': text_checks['geometry_exact_declared_000_to_142'],
                  'stored_block_text_coverage': text_checks.get('stored_exact_declared_000_to_071'),
                  'stored_block_text_maps_match': all(x['text_position_map_matches'] for x in text_checks.get('stored_block_mapping', [])),
                  'registry': pin(OUT / 'REGISTRY.json')}, ensure_ascii=False))
