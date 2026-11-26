#!/usr/bin/env python3
"""Frozen actual AG read-only acceptance collector.

Uses unchanged published AG readers and original source/receipt/artifact bindings.
ReserveBranches retains successful run0; AtlasRoughPrime retains successful run1.
No compiler, stock query, source installer, archive writer, or Git mutation is run.
"""
from pathlib import Path
from types import ModuleType
import hashlib
import json
import os
import re
import subprocess
import sys
sys.dont_write_bytecode = True
# Actual AG publication and both successful original run/owner outcomes are frozen.
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
AF = 'b06429e9c2d8fbd5c654105d5f4e44f26c0865f4'
AE = 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
RESERVEBRANCHES = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 343325, 'sha256': '0440906dfc3caa894ff7226e53ad42be54adda1d5879bd1a72cad578a3b3612d'}
MANIFEST_FP = {'bytes': 369103, 'sha256': '21c0b14701a2123edab7353aa27dbb9c950427a805d75aaa3562c6033eb137f9'}
# Frozen from actual AG RESULT/WORKER byte pins and ACTUAL_AG_METADATA.json.
# ReserveBranches 13/13 and AtlasRoughPrime 6/6 retain different accepting runs.
PINNED = {'schema': 'p15_AG_fixed_actual_collection_inputs_v1',
 'runs': [{'compiler_job': 'job_83532ebe8bdd423caa1a7610aac08ae7',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 459769,
                                           'sha256': 'ad53842b6a0189acb2357b63ce3fcc4552c85c00f6b0284e4c56c36719656b93'},
                    'CONTEXT_BEFORE.json': {'bytes': 459769,
                                            'sha256': 'ad53842b6a0189acb2357b63ce3fcc4552c85c00f6b0284e4c56c36719656b93'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 45791,
                                    'sha256': '8df860c46e8442267591dad3356f5610deee849d9c959fad38037274bf81536a'},
                    'WORKER_RESULT.json': {'bytes': 45726,
                                           'sha256': '989e9500f604e54cde2dcc0f1bc862b3b27c0da77e987219a90a5fc3c7ef4190'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'],
                     'failures': {},
                     'reused_complete_selected_owners': [],
                     'selected_live_source_count': 140,
                     'direct_import_readiness': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches']}},
          {'compiler_job': 'job_0ff7bb5706c04f94a026aee1a0d5a316',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 482694,
                                           'sha256': 'b6ea4ef3477db7dfbb6c6e961a467e5104127f3cb66ce58ef4ab7b76e2f5676f'},
                    'CONTEXT_BEFORE.json': {'bytes': 482694,
                                            'sha256': 'b6ea4ef3477db7dfbb6c6e961a467e5104127f3cb66ce58ef4ab7b76e2f5676f'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 57039,
                                    'sha256': '17770f8bf394c41f6e9ea650b9a0ee7545dcc0dfe3a82c1a6902db8486661a7e'},
                    'WORKER_RESULT.json': {'bytes': 56974,
                                           'sha256': 'a48a65e07effd868d4769ef4630bb696c4c55662572c74fdc57763d4091552c5'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                         'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
                     'failures': {},
                     'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'],
                     'selected_live_source_count': 144,
                     'direct_import_readiness': ['ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']}}],
 'owners': {'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': {'accepting_run_index': 0,
                                                                   'public_name': 'RESERVEBRANCHES_AG_PUBLIC_ACCEPTANCE',
                                                                   'audit_id': '3c62877f43ddf925ee34',
                                                                   'owned_count': 13,
                                                                   'public_count': 13,
                                                                   'source': {'bytes': 8197,
                                                                              'sha256': 'd5945aa39ab54bc5c4aeb529a96299e7ab3bcf0c4fcb946296d3a697753a2bb7'},
                                                                   'audit_result': {'bytes': 22759,
                                                                                    'sha256': '4a119123eb7472c0086055afb399262e426eeb7e48e3127d2e736117d2957359'},
                                                                   'owner_live_source_closure_count': 140},
            'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime': {'accepting_run_index': 1,
                                                                  'public_name': 'ATLASROUGHPRIME_AG_PUBLIC_ACCEPTANCE',
                                                                  'audit_id': 'bde2141e3b95bd7e5707',
                                                                  'owned_count': 6,
                                                                  'public_count': 6,
                                                                  'source': {'bytes': 7431,
                                                                             'sha256': 'dca0a3c5eab650f5329c2cf1159af676d4d3c44d1b86dd2ee158e596aa55a57d'},
                                                                  'audit_result': {'bytes': 23228,
                                                                                   'sha256': '81f621b90e7f2693cfe6eb817feb8c0364049846247cfa60147544c0907f8c14'},
                                                                  'owner_live_source_closure_count': 144}},
 'extra_pins': {'/workspace/p1-complete-proof/20261126-p15-lowertrim-api-repair-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 549208,
                                                                                                                                                                            'sha256': '73cf0272db2e0e33c40462de795e6dc97c0c7b6ae4703b96fb0c94e1d4f31b03'},
                '/workspace/p1-complete-proof/20261126-p15-mean-api-repair-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 530642,
                                                                                                                                                                       'sha256': '32861aa7155d2e3f2e7a85bfed7d340759d2a0730784ef67134c24e21af8b363'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/ACTUAL_SYNTHESIS_PROBE_RESULT.json': {'bytes': 5727,
                                                                                                                                                                                    'sha256': '1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/OriginalSharpPrimeSynthesisProbe.lean': {'bytes': 14464,
                                                                                                                                                                                       'sha256': '40b0bc9e5680cf83cd0769b299f19c1d7fcc2332ef11f5504a6b5617290ebd1e'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/serialized-whole-synthesis-probe.log': {'bytes': 3579,
                                                                                                                                                                                      'sha256': 'c722c9da32531e45ad53be48753c8dad2bb52434c392588bf2b90bd23b2bf398'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-repair-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 539949,
                                                                                                                                                                            'sha256': '1f0815dbb5409e66f4b890eed13a3ad3ebd919130c5544aee37adf3da3d50bbd'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/normal/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/attempt-00000/normal-command.json': {'bytes': 1318,
                                                                                                                                                                                                                                                                             'sha256': 'a450854359288c2c10eb99178c44fc12b57ed86bfb13597f1cc99ccb6d2876a6'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/normal/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/attempt-00000/normal.log': {'bytes': 196840,
                                                                                                                                                                                                                                                                    'sha256': 'ba220ef31dbefca82c4bd3e1297980cb99d70d22024daf93d30ab09cdb7b7a92'},
                '/workspace/p1-complete-proof/20261126-p15-reservebranches-api-repair-v1/63ad8bf4c52caed9f4e199834ae1d2b0b18f971b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 503796,
                                                                                                                                                                                  'sha256': 'b3ab010937a2baafd2a4b1b46e7a9a62c867bbb47d1ef5fbd84202f806fbb9cc'}},
 'failed_artifact_observations': {},
 'current_read_live_source_count': 144,
 'current_read_preserved_dependency_count': 142}
CLAIMS = dict(normal_or_kernel_commands_executed=0, stock_readiness_executed_by_collector=False,
    types_or_archives_exported=False, axiom_union_exported=False, new_lean_acceptance=False,
    whole_P1_5_complete=False)
stage = 'require_frozen_actual_AG_evidence'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def value_fp(value):
    return raw_fp((json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode())


def pin(value):
    return {k: value[k] for k in ('bytes', 'sha256')}


def file_fp(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'required regular evidence missing: '+str(path))
    with path.open('rb') as stream:
        return {'bytes': os.fstat(stream.fileno()).st_size, 'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}


def bind(path):
    return {'path': str(path), **file_fp(path)}


def tree_inventory(base):
    need(base.is_dir() and base.resolve() == base, 'original evidence root differs')
    result = {}
    for path in sorted(base.rglob('*')):
        need(not path.is_symlink(), 'symlink in original evidence tree')
        result[str(path.relative_to(base))] = 'directory' if path.is_dir() else file_fp(path)
    return result


def validate_scope(result, worker, scope):
    targets, accepted, failed, reused = [scope[k] for k in
        ('targets', 'accepted_owners', 'failures', 'reused_complete_selected_owners')]
    need(targets and len(targets) == len(set(targets)) and accepted == targets[:len(accepted)] and
         len(accepted) <= len(targets) and reused == [m for m in accepted if m in reused] and
         len(reused) == len(set(reused)), 'invalid frozen accepted prefix')
    complete = len(accepted) == len(targets)
    need((not failed) if complete else list(failed) == [targets[len(accepted)]], 'failure is not the first unaccepted owner')
    for record in (result, worker):
        need(record['source_commit'] == AG and record['published_source_count'] == 360 and
             all(record[k] == scope[k] for k in ('targets', 'accepted_owners', 'failures',
                 'reused_complete_selected_owners', 'selected_live_source_count')) and
             set(record['acceptance_bindings']) == set(accepted) and
             set(record['direct_import_readiness']) == set(scope['direct_import_readiness']) and
             all(record[k] is False for k in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not {'context_error', 'final_context_error', 'git_error'} & record.keys(), 'original AG scope differs')
    need(all(result.get(k) == v for k, v in worker.items()) and
         result['worker_exit_code'] == (0 if complete else 1) and
         result['all_selected_owners_accepted'] is complete, 'original AG terminal status differs')
    need(('dispatch_error' not in result and 'final_stock_readiness' in worker) if complete else
         (result.get('dispatch_error') == 'serialized worker exited 1' and
          'final_stock_readiness' not in result and 'final_stock_readiness' not in worker), 'original final-stock status differs')
    return complete


def accepting_runs(runs):
    origins = {}
    for index, (result, _, _) in enumerate(runs):
        reused = result['reused_complete_selected_owners']
        for module in result['accepted_owners']:
            if module in origins:
                need(module in reused and result['acceptance_bindings'][module] ==
                     runs[origins[module]][0]['acceptance_bindings'][module], 'same-AG reuse differs from first acceptance')
            else:
                need(module not in reused, 'reused owner lacks its original accepting run')
                origins[module] = index
    need(runs[0][0]['targets'] == [RESERVEBRANCHES], 'ReserveBranches first-run target identity differs')
    return origins


def read_run(driver, s, graph, index, fixed):
    run = ROOT / AG / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py'] + [
        stem+'_'+side+'.json' for stem in ('CONTEXT', 'GIT') for side in ('BEFORE', 'AFTER')]
    files = {name: bind(run/name) for name in names}
    need(set(fixed['pins']) == set(names)-{'executed-driver.py'} and
         all(pin(files[name]) == wanted for name, wanted in fixed['pins'].items()) and
         pin(files['executed-driver.py']) == DRIVER_FP, 'original AG run pins differ')
    result, worker, context = [s.api.read_json(run/name) for name in
        ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
    complete = validate_scope(result, worker, fixed['scope'])
    for stem in ('CONTEXT', 'GIT'):
        need(pin(files[stem+'_BEFORE.json']) == pin(files[stem+'_AFTER.json']), 'original context/Git pair changed')
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == AG and context['committed_inputs']['source_anchor_commit'] == AF and
         driver.selection(requested) == requested and set(requested) == set(result['targets']) and
         s.d.compile_order([], requested, graph) == result['targets'], 'requested/executed AG scope differs')
    stock = {'recorded': False, 'reason': 'original_attempt_stopped_after_owner_failure', 'executed_again_by_collector': False}
    if complete:
        rec = result['final_stock_readiness']
        need(rec == s.api.read_json(run/'final-stock-readiness-command.json') and rec['exit_code'] == 0 and
             rec['actual_built_modules'] == rec['actual_failed_modules'] == [] and rec['cwd'] == str(PROJECT) and
             rec['argv'] == s.h.guard(0, ['lake', '--no-build', 'build']+['+'+m+':olean' for m in result['targets']]) and
             rec['log'] == str(run/'final-stock-readiness.log') and
             file_fp(rec['log']) == {'bytes': rec['log_bytes'], 'sha256': rec['log_sha256']}, 'original stock command/log differs')
        stock = {'recorded': True, 'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': [],
            'command': bind(run/'final-stock-readiness-command.json'), 'log': bind(rec['log']), 'executed_again_by_collector': False}
    public = {k: result[k] for k in ('source_commit', 'targets', 'accepted_owners',
        'reused_complete_selected_owners', 'worker_exit_code', 'all_selected_owners_accepted')}
    n = len(result['accepted_owners'])
    public.update(compiler_job=fixed['compiler_job'], original_run=str(run), original_requested_targets=requested,
        status='ALL_SELECTED_OWNERS_ACCEPTED' if complete else 'PARTIAL_FAILURE_AFTER_ACCEPTED_PREFIX',
        failed_modules=list(result['failures']), failure_messages=result['failures'],
        not_accepted_modules=result['targets'][n:], not_started_modules=[] if complete else result['targets'][n+1:],
        dispatch_error=result.get('dispatch_error'), original_live_source_count=result['selected_live_source_count'],
        evidence_bindings=files, original_context_pairs_equal=True, original_final_stock_readiness=stock)
    return result, context, public


def read_owner(driver, s, spec, runs, module, index, fixed):
    driver.require_completed_existing_owner(s, AG, spec, module, spec.initial_owners[module])
    binding = driver.acceptance_binding(s, AG, module)
    need(binding == runs[index][0]['acceptance_bindings'][module], 'live owner binding differs from original accepting run')
    folder = ROOT/AG/module
    audit = folder/'audits'/fixed['audit_id']
    paths = {'normal': folder/'normal'/module/'NORMAL_PASS.json', 'audit_plan': audit/'AUDIT_PLAN.json',
        'audit_result': audit/'lane-0/VALIDATION_RESULTS.json', 'owned_exports': audit/'lane-0/OWNED_EXPORTS.json',
        'owned_log': audit/'lane-0/all-owned-types-axioms.log', 'reused_normal_evidence': audit/'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    receipts = {key: bind(path) for key, path in paths.items()}
    need(binding['normal_receipt'] == receipts['normal'] and binding['audits'] == [
         {'plan': receipts['audit_plan'], 'result': receipts['audit_result']}] and
         pin(receipts['audit_result']) == fixed['audit_result'], 'fixed owner audit identity differs')
    counted = s.api.read_json(paths['audit_result'])
    counts = (counted['total_owned_exports'], counted['total_public_exports'])
    need(counts == (fixed['owned_count'], fixed['public_count']), 'fixed owner counts differ')
    source = PROJECT/s.h.module_path(module)
    own_closure = len(s.h.closure(spec.graph, [module]))
    need(file_fp(source) == fixed['source'] and spec.sources[module] == fixed['source']['sha256'] and
         own_closure == fixed['owner_live_source_closure_count'], 'fixed owner source/closure differs')
    later_reuse = [r[2]['original_run'] for j, r in enumerate(runs) if j > index and
                   module in r[0]['reused_complete_selected_owners']]
    need(len(later_reuse) <= 1, 'unexpected later reuse run count')
    return {'source_commit': AG, 'source_sha256': spec.sources[module], 'source': bind(source),
        'compiler_job': runs[index][2]['compiler_job'], 'original_accepting_run': runs[index][2]['original_run'],
        'audit_id': fixed['audit_id'], 'owned_count': counts[0], 'public_count': counts[1],
        'owner_live_source_closure_count': own_closure,
        'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
        'receipt_paths': {key: value['path'] for key, value in receipts.items()},
        'normal_kernel_full_owned_revalidated_without_execution': True,
        'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
        'receipt_rebound_to_current_commit': False, 'later_same_AG_reuse_run': later_reuse[0] if later_reuse else None}


def identity(spec, selected):
    return dict(source_commit=AG, source_anchor_commit=AF, driver={'commit': AG, 'path': DRIVER, **DRIVER_FP},
        source_manifest={'commit': AG, 'path': MANIFEST, **MANIFEST_FP}, published_source_count=len(spec.graph),
        selected_owners_revalidated=selected, current_read_live_source_count=len(spec.active),
        current_read_preserved_dependency_count=len(spec.dependency_pins))


def flat_summary(runs, index, module, owner, common):
    run = runs[index][2]; files = run['evidence_bindings']
    groups = {k: run[k] for k in ('accepted_owners', 'reused_complete_selected_owners', 'failed_modules',
        'not_accepted_modules', 'not_started_modules', 'worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    return {**common, **CLAIMS, 'schema': 'p15_AG_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_AG_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'compiler_job': run['compiler_job'],
        'original_run': 'runs/attempt-%05d' % index, 'original_result': pin(files['RESULT.json']),
        'original_worker_result': pin(files['WORKER_RESULT.json']), 'original_requested_targets': run['original_requested_targets'],
        'original_targets': run['targets'], **{'original_group_'+k: v for k, v in groups.items()},
        'original_group_live_closure_count': run['original_live_source_count'],
        'original_context_pairs': {stem: {side: pin(files[stem+'_'+side.upper()+'.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'], 'owners': {module: owner},
        'owner_live_source_closure_count': owner['owner_live_source_closure_count'],
        'later_same_source_reuse': runs[1][2] if owner['later_same_AG_reuse_run'] else None,
        'source_runtime_and_original_receipts_unchanged': True}


def collect():
    global stage
    need(__debug__, 'optimized Python refused')
    need(isinstance(PINNED, dict) and PINNED.get('schema') == 'p15_AG_fixed_actual_collection_inputs_v1',
         'actual AG later2 outcome and raw run/owner pins are not yet frozen')
    need(len(PINNED['runs']) == 2 and isinstance(PINNED['owners'], dict) and PINNED['owners'] and
         all(re.fullmatch('job_[0-9a-f]{32}', r['compiler_job']) for r in PINNED['runs']),
         'fixed actual runs/accepted-owner pins incomplete; no acceptance collection attempted')
    need(PINNED['runs'][0]['scope']['targets'] == [RESERVEBRANCHES] and
         PINNED['runs'][0]['scope']['selected_live_source_count'] == 140 and
         PINNED['runs'][1]['scope']['selected_live_source_count'] == 144 and
         len(PINNED['runs'][1]['scope']['targets']) == 2 and
         PINNED['runs'][1]['scope']['targets'][0] == RESERVEBRANCHES,
         'fixed AG first140/later2 source scope differs')
    # First process-environment access: unbound PINNED has already held.
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    stage = 'load_published_AG_reader'
    raw, manifest_raw = [subprocess.check_output(['git', 'show', AG+':'+path], cwd=REPO) for path in (DRIVER, MANIFEST)]
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published AG reader/manifest differs')
    executed = ROOT/AG/'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'original AG executed reader differs')
    driver = ModuleType('unchanged_AG_acceptance_reader'); driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, AF), 'AG reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    trees = {c: tree_inventory(ROOT/c) for c in (AG, AE, AC, AA, Y, W, U, S, Q)}
    extras = {p: file_fp(p) for p in PINNED['extra_pins']}
    need(extras == PINNED['extra_pins'], 'fixed extra evidence differs')
    for module, expected in PINNED['failed_artifact_observations'].items():
        need(set(expected) == set(driver.artifact_paths(module)) and driver.module_artifacts(s, module) == expected,
             'original failed owner artifact slots differ: '+module)
    manifest = json.loads(manifest_raw); graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    stage = 'read_two_original_AG_runs'
    runs = [read_run(driver, s, graph, i, fixed) for i, fixed in enumerate(PINNED['runs'])]
    need(runs[0][0]['targets'] == [RESERVEBRANCHES] and
         runs[1][0]['targets'] == manifest['selection_guidance']['subsequent_2_targets'] and
         len(manifest['previously_accepted_targets']) == 16 and
         manifest['previously_accepted_targets'] == driver.PREVIOUSLY_ACCEPTED_TARGETS,
         'first/later target scopes or sixteen inherited prior identities differ')
    origins = accepting_runs(runs); selected = list(origins)
    need(set(origins) == set(PINNED['owners']) and all(PINNED['owners'][m]['accepting_run_index'] == i for m, i in origins.items()),
         'frozen owner accepting-run mapping differs')
    names = [PINNED['owners'][m]['public_name'] for m in selected]
    need(len(names) == len(set(names)) and all(re.fullmatch('[A-Za-z0-9_]+_AG_PUBLIC_ACCEPTANCE', n) for n in names),
         'owner public-summary names collide or differ')
    stage = 'original_AG_preflight_for_actual_accepted_prefix'
    spec = driver.preflight(s, AG, selected)
    need(len(spec.graph) == 360 and len(spec.active) == PINNED['current_read_live_source_count'] and
         len(spec.dependency_pins) == PINNED['current_read_preserved_dependency_count'] and
         spec.order == selected and set(spec.initial_owners) == set(selected), 'actual accepted-prefix read scope differs')
    for result, context, _ in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active-set(result['targets']), 'original AG context inventory differs')
    remaining_failed = {m for result, _, _ in runs for m in result['failures']} - set(origins)
    need(set(PINNED['failed_artifact_observations']) == remaining_failed,
         'remaining failed-owner artifact inventory is incomplete or stale')
    failure_observations = {}
    for module in sorted(remaining_failed):
        source = PROJECT/s.h.module_path(module)
        need(str(source) in extras and extras[str(source)] ==
             {k: manifest['project_sources'][module][k] for k in ('bytes', 'sha256')},
             'failed owner source is not pinned to the original AG source: '+module)
        normal_prefix = module+'/normal/'
        failure_observations[module] = {
            'source': bind(source), 'artifact_slots': PINNED['failed_artifact_observations'][module],
            'normal_evidence': {str(ROOT/AG/path): observed for path, observed in trees[AG].items()
                                if path.startswith(normal_prefix) and observed != 'directory'},
            'normal_receipt': str(ROOT/AG/module/'normal'/module/'NORMAL_PASS.json'),
            'normal_receipt_observation': trees[AG].get(module+'/normal/'+module+'/NORMAL_PASS.json'),
            'acceptance_claimed': False}
    artifacts = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    def target_sources():
        return {m: file_fp(PROJECT/s.h.module_path(m)) if os.path.lexists(PROJECT/s.h.module_path(m)) else None for m in driver.TARGETS}
    sources_before = target_sources()
    owners = {}
    for module, index in origins.items():
        stage = 'revalidate_original_AG_owner:'+module
        owners[module] = read_owner(driver, s, spec, runs, module, index, PINNED['owners'][module])
    stage = 'verify_read_only_preservation'
    need(driver.snapshot(s, spec) == spec.baseline and target_sources() == sources_before and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts and
         {p: file_fp(p) for p in extras} == extras and {c: tree_inventory(ROOT/c) for c in trees} == trees and
         s.d.original_git_state(REPO) == git_before, 'source/runtime/artifacts/original-evidence/Git changed during collection')
    common = identity(spec, selected)
    return {**common, **CLAIMS, 'schema': 'p15_AG_original_accepted_prefix_read_v1',
        'status': 'ORIGINAL_AG_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'collector': {'filename': Path(__file__).name, **file_fp(__file__)},
        'frozen_actual_input_binding': value_fp(PINNED),
        'public_summaries': {PINNED['owners'][m]['public_name']: flat_summary(runs, origins[m], m, row, common) for m, row in owners.items()},
        'original_runs': [r[2] for r in runs],
        'historical_owners_revalidated_in_current_read_scope': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'owned_count', 'public_count')} for m, row in spec.supplier_evidence.items()},
        'complete_original_AG_AE_AC_AA_Y_W_U_S_Q_evidence_inventory': {c: {'entry_count': len(t), **value_fp(t)} for c, t in trees.items()},
        'preserved_extra_evidence': extras, 'current_read_snapshot': value_fp(spec.baseline),
        'inherited_previous_target_count': 16,
        'inherited_previous_target_manifest_binding': value_fp(manifest['previously_accepted_targets']),
        'inherited_previous_target_identities': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'live_source_closure_count')}
            for m, row in manifest['previously_accepted_targets'].items()},
        'failed_owner_observations': failure_observations,
        'current_dirty_Git_state': value_fp(git_before), 'all_current_target_artifact_slots_watched': len(driver.TARGETS)*21,
        'all_current_target_source_slots_watched': len(sources_before), 'current_target_source_inventory': value_fp(sources_before),
        'remaining_failed_modules': runs[1][2]['failed_modules'], 'remaining_not_started_modules': runs[1][2]['not_started_modules'],
        'source_runtime_artifacts_and_original_receipts_unchanged': True, 'current_dirty_Git_state_unchanged': True}


if __name__ == '__main__':
    try:
        result, code = collect(), 0
    except Exception as error:
        result = {'status': 'HOLD', 'stage': stage, 'error_type': type(error).__name__,
            'reason': str(error)[:1000], 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
        code = 3
    print(json.dumps(result, ensure_ascii=False, sort_keys=True), flush=True)
    raise SystemExit(code)
