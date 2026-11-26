#!/usr/bin/env python3
"""Frozen read-only Y acceptance collector: original actual outcomes and evidence.

Uses unchanged Y preflight and original normal/kernel/full-owned readers after binding.
Endpoint keeps its first-run identity; subsequent owners keep their accepting run.
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
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
X = '09bf8a02b4c96798930abe2826cfb27529c01ad3'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 223361, 'sha256': 'e84c943388675d65c63b701c1663f030ec3c340e22d1ee31fa1c1ada3bc67918'}
MANIFEST_FP = {'bytes': 357110, 'sha256': '25eef56e95dee4c5ef7308b49b35bf125dc79af032fd5bef0e658bed8001a04a'}
# Frozen from actual Y metadata/results: Endpoint accepted at run0 and reused at run1;
# MeanCorrection failed in run1, five following owners unstarted, no later final stock.
PINNED = {'schema': 'p15_Y_fixed_actual_collection_inputs_v1',
 'runs': [{'compiler_job': 'job_8f89803dbab64592982477c8613b24c1',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 306206,
                                           'sha256': 'c897d7f14b6c6cef66c7ccbbbd2905d13f7539af2990c3ccceaf898d0eb0dfb0'},
                    'CONTEXT_BEFORE.json': {'bytes': 306206,
                                            'sha256': 'c897d7f14b6c6cef66c7ccbbbd2905d13f7539af2990c3ccceaf898d0eb0dfb0'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 8702,
                                    'sha256': 'ee4f055634e6e56673e586fe3db1998ff10d7a45c8f99907481461292b8edb58'},
                    'WORKER_RESULT.json': {'bytes': 8637,
                                           'sha256': '744a42fc02e4fb9d9134b7a15bf38b552b0e6d51e7dbc2732baa7a85f5af3965'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                     'failures': {},
                     'reused_complete_selected_owners': [],
                     'selected_live_source_count': 110,
                     'direct_import_readiness': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment']}},
          {'compiler_job': 'job_579a949c0cfa4b85a4b678592bbc7295',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 506374,
                                           'sha256': 'cd603957864771e99195597935aebc1e822970c36ce4c02d88a4d621ef2ba22d'},
                    'CONTEXT_BEFORE.json': {'bytes': 506374,
                                            'sha256': 'cd603957864771e99195597935aebc1e822970c36ce4c02d88a4d621ef2ba22d'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 50678,
                                    'sha256': '11fe73336284239346394cd6c1480cc9cfc94a883dddfcacd71230ab3492a53d'},
                    'WORKER_RESULT.json': {'bytes': 50562,
                                           'sha256': '4a12b1cacaaa5fa6db440b79b34e9ac4b7e5c0208f2dd3dd9ac5e8340e65575b'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
                                 'ImbalancedChen.P5PrimeDivisorMeanCorrection',
                                 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                                 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                                 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                                 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                     'failures': {'ImbalancedChen.P5PrimeDivisorMeanCorrection': 'normal '
                                                                                 'failed/scope '
                                                                                 'differs: '
                                                                                 'ImbalancedChen.P5PrimeDivisorMeanCorrection'},
                     'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                     'selected_live_source_count': 157,
                     'direct_import_readiness': ['ImbalancedChen.P5PrimeDivisorMeanCorrection']}}],
 'owners': {'ImbalancedChen.P5OriginalPrimeEndpointLogPayment': {'accepting_run_index': 0,
                                                                 'public_name': 'ENDPOINT_Y_PUBLIC_ACCEPTANCE',
                                                                 'audit_id': 'a602bb782d20fdd11079',
                                                                 'owned_count': 24,
                                                                 'public_count': 24,
                                                                 'source': {'bytes': 13668,
                                                                            'sha256': '1a9baa44f798fba58671d473f3be4def2eaefd6c758413e0f7d60b3238edef3c'},
                                                                 'audit_result': {'bytes': 19033,
                                                                                  'sha256': 'daa188d393974be55aa446331beeea891d2f1b3982350d6f481bdf4a96b45ea2'},
                                                                 'owner_live_source_closure_count': 110}},
 'extra_pins': {'/workspace/p1-complete-proof/20261126-p15-endpoint-api-repair-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 521383,
                                                                                                                                                                           'sha256': '4395d60e039a34e91693b327246d2b349390d3d1242b16dfbe7714b6f2ca9846'},
                '/workspace/blue-member-build/ImbalancedChen/P5PrimeDivisorMeanCorrection.lean': {'bytes': 17065,
                                                                                                  'sha256': '1da7fe8cde7360ba7748bf1c3f85e00ad1da470a15638eb8cf4b6a32ffdfc3ee'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/ImbalancedChen.P5PrimeDivisorMeanCorrection/normal/ImbalancedChen.P5PrimeDivisorMeanCorrection/attempt-00000/normal-command.json': {'bytes': 2040,
                                                                                                                                                                                                                                                               'sha256': 'f715beeda423fe7fd1aa26a55d41d0e41e4f53cad86eb6d1e63411162cd2b280'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/ImbalancedChen.P5PrimeDivisorMeanCorrection/normal/ImbalancedChen.P5PrimeDivisorMeanCorrection/attempt-00000/normal.log': {'bytes': 186750,
                                                                                                                                                                                                                                                      'sha256': '0394e18833ead6eab9978d94f96171220c8e396c0bf533007b18eed237d77773'},
                '/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.setup.json': {'bytes': 6416378,
                                                                                                                       'sha256': 'e51ad84eea0a873a4414e09a754beaaf1eb4caca2632d7c56a8bc2a0921d4675'}},
 'failed_artifact_observations': {'ImbalancedChen.P5PrimeDivisorMeanCorrection': {'.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.bc': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.bc.hash': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.c': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.c.hash': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.o': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.o.export': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.o.export.hash': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.o.hash': None,
                                                                                  '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.setup.json': {'bytes': 6416378,
                                                                                                                                                            'sha256': 'e51ad84eea0a873a4414e09a754beaaf1eb4caca2632d7c56a8bc2a0921d4675'},
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.ilean': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.ilean.hash': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.ir': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.ir.hash': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.ir.sig': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.olean': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.olean.hash': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.olean.private': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.olean.private.hash': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.olean.server': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.olean.server.hash': None,
                                                                                  '.lake/build/lib/lean/ImbalancedChen/P5PrimeDivisorMeanCorrection.trace': None}},
 'current_read_live_source_count': 110,
 'current_read_preserved_dependency_count': 109}
CLAIMS = dict(normal_or_kernel_commands_executed=0, stock_readiness_executed_by_collector=False,
    types_or_archives_exported=False, axiom_union_exported=False, new_lean_acceptance=False,
    whole_P1_5_complete=False)
stage = 'require_frozen_actual_Y_evidence'


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
        need(record['source_commit'] == Y and record['published_source_count'] == 360 and
             all(record[k] == scope[k] for k in ('targets', 'accepted_owners', 'failures',
                 'reused_complete_selected_owners', 'selected_live_source_count')) and
             set(record['acceptance_bindings']) == set(accepted) and
             set(record['direct_import_readiness']) == set(scope['direct_import_readiness']) and
             all(record[k] is False for k in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not {'context_error', 'final_context_error', 'git_error'} & record.keys(), 'original Y scope differs')
    need(all(result.get(k) == v for k, v in worker.items()) and
         result['worker_exit_code'] == (0 if complete else 1) and
         result['all_selected_owners_accepted'] is complete, 'original Y terminal status differs')
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
                     runs[origins[module]][0]['acceptance_bindings'][module], 'same-Y reuse differs from first acceptance')
            else:
                need(module not in reused, 'reused owner lacks its original accepting run')
                origins[module] = index
    need(runs[0][0]['targets'] == [ENDPOINT], 'Endpoint first-run target identity differs')
    return origins


def read_run(driver, s, graph, index, fixed):
    run = ROOT / Y / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py'] + [
        stem+'_'+side+'.json' for stem in ('CONTEXT', 'GIT') for side in ('BEFORE', 'AFTER')]
    files = {name: bind(run/name) for name in names}
    need(set(fixed['pins']) == set(names)-{'executed-driver.py'} and
         all(pin(files[name]) == wanted for name, wanted in fixed['pins'].items()) and
         pin(files['executed-driver.py']) == DRIVER_FP, 'original Y run pins differ')
    result, worker, context = [s.api.read_json(run/name) for name in
        ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
    complete = validate_scope(result, worker, fixed['scope'])
    for stem in ('CONTEXT', 'GIT'):
        need(pin(files[stem+'_BEFORE.json']) == pin(files[stem+'_AFTER.json']), 'original context/Git pair changed')
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == Y and context['committed_inputs']['source_anchor_commit'] == X and
         driver.selection(requested) == requested and set(requested) == set(result['targets']) and
         s.d.compile_order([], requested, graph) == result['targets'], 'requested/executed Y scope differs')
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
    driver.require_completed_existing_owner(s, Y, spec, module, spec.initial_owners[module])
    binding = driver.acceptance_binding(s, Y, module)
    need(binding == runs[index][0]['acceptance_bindings'][module], 'live owner binding differs from original accepting run')
    folder = ROOT/Y/module
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
    return {'source_commit': Y, 'source_sha256': spec.sources[module], 'source': bind(source),
        'compiler_job': runs[index][2]['compiler_job'], 'original_accepting_run': runs[index][2]['original_run'],
        'audit_id': fixed['audit_id'], 'owned_count': counts[0], 'public_count': counts[1],
        'owner_live_source_closure_count': own_closure,
        'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
        'receipt_paths': {key: value['path'] for key, value in receipts.items()},
        'normal_kernel_full_owned_revalidated_without_execution': True,
        'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
        'receipt_rebound_to_current_commit': False, 'later_same_Y_reuse_run': later_reuse[0] if later_reuse else None}


def identity(spec, selected):
    return dict(source_commit=Y, source_anchor_commit=X, driver={'commit': Y, 'path': DRIVER, **DRIVER_FP},
        source_manifest={'commit': Y, 'path': MANIFEST, **MANIFEST_FP}, published_source_count=len(spec.graph),
        selected_owners_revalidated=selected, current_read_live_source_count=len(spec.active),
        current_read_preserved_dependency_count=len(spec.dependency_pins))


def flat_summary(runs, index, module, owner, common):
    run = runs[index][2]; files = run['evidence_bindings']
    groups = {k: run[k] for k in ('accepted_owners', 'reused_complete_selected_owners', 'failed_modules',
        'not_accepted_modules', 'not_started_modules', 'worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    return {**common, **CLAIMS, 'schema': 'p15_Y_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_Y_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'compiler_job': run['compiler_job'],
        'original_run': 'runs/attempt-%05d' % index, 'original_result': pin(files['RESULT.json']),
        'original_worker_result': pin(files['WORKER_RESULT.json']), 'original_requested_targets': run['original_requested_targets'],
        'original_targets': run['targets'], **{'original_group_'+k: v for k, v in groups.items()},
        'original_group_live_closure_count': run['original_live_source_count'],
        'original_context_pairs': {stem: {side: pin(files[stem+'_'+side.upper()+'.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'], 'owners': {module: owner},
        'owner_live_source_closure_count': owner['owner_live_source_closure_count'],
        'later_same_source_reuse': runs[1][2] if owner['later_same_Y_reuse_run'] else None,
        'source_runtime_and_original_receipts_unchanged': True}


def collect():
    global stage
    need(__debug__, 'optimized Python refused')
    need(isinstance(PINNED, dict) and PINNED.get('schema') == 'p15_Y_fixed_actual_collection_inputs_v1',
         'actual Y later7 outcome and raw run/owner pins are not yet frozen')
    need(len(PINNED['runs']) == 2 and isinstance(PINNED['owners'], dict) and PINNED['owners'] and
         all(re.fullmatch('job_[0-9a-f]{32}', r['compiler_job']) for r in PINNED['runs']),
         'fixed actual runs/accepted-owner pins incomplete; no acceptance collection attempted')
    need(PINNED['runs'][0]['scope']['targets'] == [ENDPOINT] and
         PINNED['runs'][0]['scope']['selected_live_source_count'] == 110 and
         PINNED['runs'][1]['scope']['selected_live_source_count'] == 157 and
         len(PINNED['runs'][1]['scope']['targets']) == 7 and
         PINNED['runs'][1]['scope']['targets'][0] == ENDPOINT,
         'fixed Y first110/later7 source scope differs')
    # First process-environment access: unbound PINNED has already held.
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    stage = 'load_published_Y_reader'
    raw, manifest_raw = [subprocess.check_output(['git', 'show', Y+':'+path], cwd=REPO) for path in (DRIVER, MANIFEST)]
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published Y reader/manifest differs')
    executed = ROOT/Y/'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'original Y executed reader differs')
    driver = ModuleType('unchanged_Y_acceptance_reader'); driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, X), 'Y reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    trees = {c: tree_inventory(ROOT/c) for c in (Y, W, U, S, Q)}
    extras = {p: file_fp(p) for p in PINNED['extra_pins']}
    need(extras == PINNED['extra_pins'], 'fixed extra evidence differs')
    for module, expected in PINNED['failed_artifact_observations'].items():
        need(set(expected) == set(driver.artifact_paths(module)) and driver.module_artifacts(s, module) == expected,
             'original failed owner artifact slots differ: '+module)
    manifest = json.loads(manifest_raw); graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    stage = 'read_two_original_Y_runs'
    runs = [read_run(driver, s, graph, i, fixed) for i, fixed in enumerate(PINNED['runs'])]
    need(runs[0][0]['targets'] == [ENDPOINT] and
         runs[1][0]['targets'] == manifest['selection_guidance']['subsequent_7_targets'] and
         len(manifest['previously_accepted_targets']) == 11 and
         manifest['previously_accepted_targets'] == driver.PREVIOUSLY_ACCEPTED_TARGETS,
         'first/later target scopes or eleven inherited prior identities differ')
    origins = accepting_runs(runs); selected = list(origins)
    need(set(origins) == set(PINNED['owners']) and all(PINNED['owners'][m]['accepting_run_index'] == i for m, i in origins.items()),
         'frozen owner accepting-run mapping differs')
    names = [PINNED['owners'][m]['public_name'] for m in selected]
    need(len(names) == len(set(names)) and all(re.fullmatch('[A-Za-z0-9_]+_Y_PUBLIC_ACCEPTANCE', n) for n in names),
         'owner public-summary names collide or differ')
    stage = 'original_Y_preflight_for_actual_accepted_prefix'
    spec = driver.preflight(s, Y, selected)
    need(len(spec.graph) == 360 and len(spec.active) == PINNED['current_read_live_source_count'] and
         len(spec.dependency_pins) == PINNED['current_read_preserved_dependency_count'] and
         spec.order == selected and set(spec.initial_owners) == set(selected), 'actual accepted-prefix read scope differs')
    for result, context, _ in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active-set(result['targets']), 'original Y context inventory differs')
    remaining_failed = {m for result, _, _ in runs for m in result['failures']} - set(origins)
    need(set(PINNED['failed_artifact_observations']) == remaining_failed,
         'remaining failed-owner artifact inventory is incomplete or stale')
    failure_observations = {}
    for module in sorted(remaining_failed):
        source = PROJECT/s.h.module_path(module)
        need(str(source) in extras and extras[str(source)] ==
             {k: manifest['project_sources'][module][k] for k in ('bytes', 'sha256')},
             'failed owner source is not pinned to the original Y source: '+module)
        normal_prefix = module+'/normal/'
        failure_observations[module] = {
            'source': bind(source), 'artifact_slots': PINNED['failed_artifact_observations'][module],
            'normal_evidence': {str(ROOT/Y/path): observed for path, observed in trees[Y].items()
                                if path.startswith(normal_prefix) and observed != 'directory'},
            'normal_receipt': str(ROOT/Y/module/'normal'/module/'NORMAL_PASS.json'),
            'normal_receipt_observation': trees[Y].get(module+'/normal/'+module+'/NORMAL_PASS.json'),
            'acceptance_claimed': False}
    artifacts = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    def target_sources():
        return {m: file_fp(PROJECT/s.h.module_path(m)) if os.path.lexists(PROJECT/s.h.module_path(m)) else None for m in driver.TARGETS}
    sources_before = target_sources()
    owners = {}
    for module, index in origins.items():
        stage = 'revalidate_original_Y_owner:'+module
        owners[module] = read_owner(driver, s, spec, runs, module, index, PINNED['owners'][module])
    stage = 'verify_read_only_preservation'
    need(driver.snapshot(s, spec) == spec.baseline and target_sources() == sources_before and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts and
         {p: file_fp(p) for p in extras} == extras and {c: tree_inventory(ROOT/c) for c in trees} == trees and
         s.d.original_git_state(REPO) == git_before, 'source/runtime/artifacts/original-evidence/Git changed during collection')
    common = identity(spec, selected)
    return {**common, **CLAIMS, 'schema': 'p15_Y_original_accepted_prefix_read_v1',
        'status': 'ORIGINAL_Y_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'collector': {'filename': Path(__file__).name, **file_fp(__file__)},
        'frozen_actual_input_binding': value_fp(PINNED),
        'public_summaries': {PINNED['owners'][m]['public_name']: flat_summary(runs, origins[m], m, row, common) for m, row in owners.items()},
        'original_runs': [r[2] for r in runs],
        'historical_owners_revalidated_in_current_read_scope': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'owned_count', 'public_count')} for m, row in spec.supplier_evidence.items()},
        'complete_original_Y_W_U_S_Q_evidence_inventory': {c: {'entry_count': len(t), **value_fp(t)} for c, t in trees.items()},
        'preserved_extra_evidence': extras, 'current_read_snapshot': value_fp(spec.baseline),
        'inherited_previous_target_count': 11,
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
