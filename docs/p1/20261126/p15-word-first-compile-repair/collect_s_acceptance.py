#!/usr/bin/env python3
"""Read the original S Family acceptance and later reuse; never execute a build."""
from pathlib import Path
from types import ModuleType
import base64
import hashlib
import json
import os
import subprocess
import sys

sys.dont_write_bytecode = True
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
R = '0935516b9bd978a61248c81b59776d1eb47f6044'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 130643, 'sha256': 'fdd3218c5e5d3169bd42ca8ba1953c8378f9b2c436107ed165a13068a48d2c55'}
MANIFEST_FP = {'bytes': 346806, 'sha256': '1c6d8499822f69f35469c4bbc222f85d1e46d6a5c977bd4f5c4cdd649520ba86'}
FAMILY = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
TARGETS = [FAMILY, WORD, 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence', 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection', 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid', 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches', 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
JOBS = ['job_bf1ad9f0adbc4c8a9fe4b05e99addf4d', 'job_fe03565fc9d94e01a9f87ba314af1933']
AUDIT = 'b2f9953a401fa5dd488b'
SOURCE_FP = {'bytes': 19563, 'sha256': '4f58683304250030edbca5d1ed4f27eaa06c6de18fb0bbdcad4b2101df0ab109'}
AUDIT_FP = {'bytes': 15302, 'sha256': '2512ce31e3dac3bb502a0965077910957be577c1b7210e6d8b325a84d4f37a30'}
RUN_PINS = [
    {'RESULT': (37042, '554af002bced1b2b2fcfa71834dfc3412684d9214106742d5d0a927dd57546f7'),
     'WORKER_RESULT': (36977, 'a456196896172094854f8f6d22dfcd0afa32afd3329e503620c9e4a5623e6548'),
     'CONTEXT': (255571, '016be32ebb9ee46fb8dc18e050cb82e18e704e8d41fd4b499e9f00c3fc9e600a')},
    {'RESULT': (43984, '5e909125e1e23eeca59699eb4ff834e2abde2ce148a8530863283101e2586bfc'),
     'WORKER_RESULT': (43868, 'f3bc0dbb2fe93c8b1090b34da8ad81f37bcce1192dd137cafe2912c83e08fc4b'),
     'CONTEXT': (474301, '6e1db877be24eb5b46e21176be223573214267e461bffacdf9a9f2dd79f6607b')},
]
GIT_PIN = (1157, 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e')
EXTRA_PINS = {
    str(PROJECT / 'ImbalancedChen/P5IndependentPrimeSourceWordDictionary.lean'):
        (5613, '8fd465024656d9cc3998b7f810d92ab6316f50c1817f0736e6bb0f88021d49b1'),
    str(PROJECT / '.lake/build/ir/ImbalancedChen/P5IndependentPrimeSourceWordDictionary.setup.json'):
        (6329802, '0ab1595e7cb434fea199eefea3f7e041db1e24f030858dbfa50304c4ba07c6bf'),
    str(ROOT / S / WORD / 'normal' / WORD / 'attempt-00000/normal-command.json'):
        (1673, '558f5d35401ab630543a1d1c4d246c152a61389f359cafa74c4e390b9b78b190'),
    '/workspace/p1-complete-proof/20261126-p15-family-api-repair-v1/' + S + '/runs/attempt-00000/SOURCE_REPAIR_RESULT.json':
        (486266, '93d968498440938d80580ff4f142b6f3f30bb8e8aaf42105a68b54e999c432f8'),
}
IDENTITY = dict(source_commit=S, source_anchor_commit=R,
    driver={'commit': S, 'path': DRIVER, **DRIVER_FP},
    source_manifest={'commit': S, 'path': MANIFEST, **MANIFEST_FP}, published_source_count=360,
    selected_owners_revalidated=[FAMILY], current_read_live_source_count=75, current_read_preserved_dependency_count=74)
CLAIMS = dict(normal_or_kernel_commands_executed=0, types_or_archives_exported=False,
    axiom_union_exported=False, new_lean_acceptance=False, whole_P1_5_complete=False)
PROBE = Path('/workspace/p1-complete-proof/20261126-p15-word-api-probe-v1') / S / 'runs/attempt-00000/ACTUAL_WORD_PROBE_RESULT.json'
CANDIDATE_FP = {'bytes': 5672, 'sha256': '021c39e9439f5e304e752093a332f66e68902b1a42a697c5ad4eda2ee29f648f'}
stage = 'load_published_S_reader' 


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def fp_pair(pair):
    return dict(zip(('bytes', 'sha256'), pair))


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def value_fp(value):
    return raw_fp((json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode())


def file_fp(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'required regular file missing: ' + str(path))
    with path.open('rb') as stream:
        return {'bytes': os.fstat(stream.fileno()).st_size, 'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}


def bind(path):
    return {'path': str(path), **file_fp(path)}


def pin(binding):
    return {key: binding[key] for key in ('bytes', 'sha256')}


def tree_inventory(base):
    need(base.is_dir() and base.resolve() == base, 'evidence root differs: ' + str(base))
    result = {}
    for path in sorted(base.rglob('*')):
        need(not path.is_symlink(), 'symlink in original evidence tree')
        result[str(path.relative_to(base))] = 'directory' if path.is_dir() else file_fp(path)
    return result


def validate_scope(result, worker, index):
    expected = dict(source_commit=S, targets=[FAMILY] if index == 0 else TARGETS,
        accepted_owners=[FAMILY], failures={} if index == 0 else {WORD: 'normal failed/scope differs: ' + WORD},
        reused_complete_selected_owners=[] if index == 0 else [FAMILY],
        published_source_count=360, selected_live_source_count=75 if index == 0 else 157)
    for record in (result, worker):
        need(all(record[k] == v for k, v in expected.items()) and set(record['acceptance_bindings']) == {FAMILY} and
             set(record['direct_import_readiness']) == ({FAMILY} if index == 0 else {WORD}) and
             all(record[k] is False for k in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not {'context_error', 'final_context_error', 'git_error'} & record.keys(), 'S run scope differs')
    need(all(result.get(k) == v for k, v in worker.items()) and result['worker_exit_code'] == index and
         result['all_selected_owners_accepted'] is (index == 0), 'S terminal status differs')
    need(('dispatch_error' not in result and 'final_stock_readiness' in worker) if index == 0 else
         (result.get('dispatch_error') == 'serialized worker exited 1' and
          'final_stock_readiness' not in worker and 'final_stock_readiness' not in result), 'S final stock/status differs')
    return expected['targets']


def read_run(driver, s, graph, index):
    run = ROOT / S / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py']
    names += [stem + '_' + side + '.json' for stem in ('CONTEXT', 'GIT') for side in ('BEFORE', 'AFTER')]
    files = {name: bind(run / name) for name in names}
    need(pin(files['executed-driver.py']) == DRIVER_FP, 'executed S driver differs')
    for stem, expected in {**RUN_PINS[index], 'GIT': GIT_PIN}.items():
        for suffix in (('_BEFORE', '_AFTER') if stem in ('CONTEXT', 'GIT') else ('',)):
            need(pin(files[stem + suffix + '.json']) == fp_pair(expected), 'original S evidence pin differs: ' + stem)
    result, worker, context = [s.api.read_json(run / name) for name in
        ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
    targets = validate_scope(result, worker, index)
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == S and
         context['committed_inputs']['source_anchor_commit'] == R and
         driver.selection(requested) == requested and set(requested) == set(targets) and
         s.d.compile_order([], requested, graph) == targets, 'original requested/executed scope differs')
    stock = {'recorded': False, 'reason': 'original_attempt_stopped_after_owner_failure', 'executed_again_by_collector': False}
    if index == 0:
        rec = result['final_stock_readiness']
        need(rec == s.api.read_json(run / 'final-stock-readiness-command.json') and
             rec['exit_code'] == 0 and rec['actual_built_modules'] == rec['actual_failed_modules'] == [] and
             rec['cwd'] == str(PROJECT) and
             rec['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + FAMILY + ':olean']) and
             rec['log'] == str(run / 'final-stock-readiness.log') and
             file_fp(rec['log']) == {'bytes': rec['log_bytes'], 'sha256': rec['log_sha256']},
             'original Family final stock differs')
        stock = {'recorded': True, 'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': [],
            'command': bind(run / 'final-stock-readiness-command.json'), 'log': bind(rec['log']),
            'executed_again_by_collector': False}
    public = {k: result[k] for k in ('source_commit', 'targets', 'accepted_owners',
        'reused_complete_selected_owners', 'worker_exit_code', 'all_selected_owners_accepted')}
    public.update(compiler_job=JOBS[index], original_run=str(run), original_requested_targets=requested,
        status='ALL_SELECTED_OWNERS_ACCEPTED' if index == 0 else 'PARTIAL_FAILURE_AFTER_ACCEPTED_PREFIX',
        failed_modules=list(result['failures']), failure_messages=result['failures'],
        not_accepted_modules=targets[1:], not_started_modules=targets[2:], dispatch_error=result.get('dispatch_error'),
        original_live_source_count=result['selected_live_source_count'], evidence_bindings=files,
        original_context_pairs_equal=True, original_final_stock_readiness=stock)
    return result, context, public


def flat_summary(runs, owner):
    run = runs[0][2]
    files = run['evidence_bindings']
    groups = {key: run[key] for key in ('accepted_owners', 'reused_complete_selected_owners',
        'failed_modules', 'not_accepted_modules', 'not_started_modules', 'worker_exit_code',
        'all_selected_owners_accepted', 'dispatch_error')}
    return {**IDENTITY, **CLAIMS, 'schema': 'p15_S_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_S_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'compiler_job': JOBS[0],
        'original_run': 'runs/attempt-00000', 'original_result': pin(files['RESULT.json']),
        'original_worker_result': pin(files['WORKER_RESULT.json']),
        'original_requested_targets': run['original_requested_targets'], 'original_targets': [FAMILY],
        **{'original_group_' + k: v for k, v in groups.items()}, 'original_group_live_closure_count': 75,
        'original_context_pairs': {stem: {side: pin(files[stem + '_' + side.upper() + '.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'],
        'later_same_source_reuse': runs[1][2], 'owners': {FAMILY: owner}, 'owner_live_source_closure_count': 75,
        'source_runtime_and_original_receipts_unchanged': True}


def collect():
    global stage
    need(__debug__, 'optimized Python refused')
    raw, manifest_raw = [subprocess.check_output(['git', 'show', S + ':' + path], cwd=REPO)
                         for path in (DRIVER, MANIFEST)]
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published S reader/manifest differs')
    executed = ROOT / S / 'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'first S executed reader differs')
    driver = ModuleType('unchanged_S_acceptance_reader')
    driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, R), 'S reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    trees = {commit: tree_inventory(ROOT / commit) for commit in (S, Q)}
    extras = {path: file_fp(path) for path in EXTRA_PINS}
    need(extras == {path: fp_pair(pair) for path, pair in EXTRA_PINS.items()}, 'failed setup/source or original evidence differs')
    graph = {m: row['imports'] for m, row in json.loads(manifest_raw)['project_sources'].items()}
    stage = 'read_two_original_S_runs'
    runs = [read_run(driver, s, graph, index) for index in (0, 1)]
    need(runs[0][0]['acceptance_bindings'][FAMILY] == runs[1][0]['acceptance_bindings'][FAMILY], 'Family reuse differs')
    stage = 'original_S_preflight_Family_only'
    spec = driver.preflight(s, S, [FAMILY])
    need(len(spec.graph) == 360 and len(spec.active) == 75 and len(spec.dependency_pins) == 74 and
         spec.order == [FAMILY] and set(spec.initial_owners) == {FAMILY} and WORD not in spec.active,
         'Family-only read scope differs')
    for result, context, _ in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active - set(result['targets']), 'original run inventory differs')
    artifacts = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    stage = 'revalidate_original_S_Family_owner'
    driver.require_completed_existing_owner(s, S, spec, FAMILY, spec.initial_owners[FAMILY])
    binding = driver.acceptance_binding(s, S, FAMILY)
    need(binding == runs[0][0]['acceptance_bindings'][FAMILY], 'current Family acceptance differs from first S run')
    audit = ROOT / S / FAMILY / 'audits' / AUDIT
    paths = {'normal': ROOT / S / FAMILY / 'normal' / FAMILY / 'NORMAL_PASS.json',
        'audit_plan': audit / 'AUDIT_PLAN.json', 'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
        'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json', 'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
        'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    receipts = {key: bind(path) for key, path in paths.items()}
    need(binding['normal_receipt'] == receipts['normal'] and binding['audits'] == [
         {'plan': receipts['audit_plan'], 'result': receipts['audit_result']}] and
         pin(receipts['audit_result']) == AUDIT_FP, 'original Family audit ID/pin differs')
    counted = s.api.read_json(paths['audit_result'])
    need((counted['total_owned_exports'], counted['total_public_exports']) == (27, 27), 'Family counts differ')
    source = PROJECT / s.h.module_path(FAMILY)
    need(file_fp(source) == SOURCE_FP and spec.sources[FAMILY] == SOURCE_FP['sha256'], 'Family source differs')
    owner = {'source_commit': S, 'source_sha256': spec.sources[FAMILY], 'source': bind(source),
        'compiler_job': JOBS[0], 'original_accepting_run': runs[0][2]['original_run'], 'audit_id': AUDIT,
        'owned_count': 27, 'public_count': 27, 'owner_live_source_closure_count': len(s.h.closure(spec.graph, [FAMILY])),
        'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
        'receipt_paths': {key: value['path'] for key, value in receipts.items()},
        'normal_kernel_full_owned_revalidated_without_execution': True,
        'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
        'receipt_rebound_to_current_commit': False, 'later_same_S_reuse_run': runs[1][2]['original_run']}
    stage = 'read_original_Word_probe'
    probe_raw = PROBE.read_bytes()
    probe_data = json.loads(probe_raw)
    need(probe_data['schema'] == 'p15_WordDictionary_actual_whole_module_api_probe_v1' and
         probe_data['source_base_commit'] == S and probe_data['exit_code'] == 0 and
         pin(probe_data['candidate']) == CANDIDATE_FP and probe_data['output_object_requested'] is False and
         probe_data['normal_or_kernel_acceptance_claimed'] is False, 'Word no-output probe differs')
    probe = {'path': str(PROBE), **raw_fp(probe_raw), 'base64': base64.b64encode(probe_raw).decode(),
        'compiler_job': 'job_9c4192ff119349909fe379179bb9447f', 'candidate': CANDIDATE_FP}
    stage = 'verify_read_only_preservation' 
    need(driver.snapshot(s, spec) == spec.baseline and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts and
         {path: file_fp(path) for path in extras} == extras and
         {commit: tree_inventory(ROOT / commit) for commit in trees} == trees and
         file_fp(PROBE) == pin(probe) and s.d.original_git_state(REPO) == git_before, 'source/runtime/artifacts/evidence/Git changed during collection')
    return {**IDENTITY, **CLAIMS, 'schema': 'p15_S_original_family_acceptance_read_v1',
        'status': 'ORIGINAL_S_FAMILY_REVALIDATED_WITHOUT_EXECUTION',
        'collector': {'filename': Path(__file__).name, **file_fp(__file__)},
        'public_summaries': {'FAMILY_S_PUBLIC_ACCEPTANCE': flat_summary(runs, owner)},
        'original_runs': [run[2] for run in runs],
        'historical_owners_revalidated_in_current_read_scope': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'owned_count', 'public_count')} for m, row in spec.supplier_evidence.items()},
        'all_current_target_artifact_slots_watched': len(driver.TARGETS) * 21,
        'complete_original_S_and_Q_evidence_inventory': {c: {'entry_count': len(t), **value_fp(t)} for c, t in trees.items()},
        'preserved_failed_source_setup_and_original_installation': extras,
        'current_read_snapshot': value_fp(spec.baseline), 'current_dirty_Git_state': value_fp(git_before),
        'remaining_failed_modules': [WORD], 'remaining_not_started_modules': TARGETS[2:],
        'source_runtime_artifacts_and_original_receipts_unchanged': True, 'current_dirty_Git_state_unchanged': True,
        'stock_readiness_executed_by_collector': False, 'actual_word_probe_original_raw': probe}



if __name__ == '__main__':
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        result, code = collect(), 0
    except Exception as error:
        result = {'status': 'HOLD', 'stage': stage, 'error_type': type(error).__name__,
            'reason': str(error)[:1000], 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
        code = 3
    print(json.dumps(result, ensure_ascii=False, sort_keys=True), flush=True)
    raise SystemExit(code)
