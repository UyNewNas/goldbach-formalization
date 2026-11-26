#!/usr/bin/env python3
"""Frozen read-only AC acceptance collector: original actual outcomes and evidence.

Uses unchanged AC preflight and original normal/kernel/full-owned readers after binding.
Synthesis keeps its first-run identity; subsequent owners keep their accepting run.
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
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
AB = '60e6b6e18fbda5f6b0e997d15392b32100e854d9'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
SYNTHESIS = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 278990, 'sha256': '3db1965e25fbd2fe9ddf6b1af10ef1a47f479479e8a076646d6de46c3f7130b0'}
MANIFEST_FP = {'bytes': 362316, 'sha256': 'b56ca98e7c46d9e6ab9244b2fe32f15717db95a325a0ca5e52ee965d900f44c9'}
# Frozen from actual AC metadata/results: Synthesis accepted at run0 and reused at run1;
# LowerTrim failed in run1, three following owners unstarted, no later final stock.
PINNED = {'schema': 'p15_AC_fixed_actual_collection_inputs_v1',
 'runs': [{'compiler_job': 'job_b4464fff4b944230927c0f40b7cd1632',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 324560,
                                           'sha256': '04ce6b5b6f2b4220d0076ab76676a7a11ccb445440e081ba517ab06800a45730'},
                    'CONTEXT_BEFORE.json': {'bytes': 324560,
                                            'sha256': '04ce6b5b6f2b4220d0076ab76676a7a11ccb445440e081ba517ab06800a45730'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 11872,
                                    'sha256': '143b90e465f63ce485afde302aa66c4bf63f13d21d636e06862563848cbba92d'},
                    'WORKER_RESULT.json': {'bytes': 11807,
                                           'sha256': 'ceddbd34193c920757130eb916b20f933cf659b1932ee8e775d366ccc30fe556'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                     'failures': {},
                     'reused_complete_selected_owners': [],
                     'selected_live_source_count': 112,
                     'direct_import_readiness': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis']}},
          {'compiler_job': 'job_a108c4d7e2594e1fb5a674382db6600f',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 524382,
                                           'sha256': 'c45a4363cc4bac2ff74740fcbc4e8c69a339b185cbba0e2cf9f67f9377cba257'},
                    'CONTEXT_BEFORE.json': {'bytes': 524382,
                                            'sha256': 'c45a4363cc4bac2ff74740fcbc4e8c69a339b185cbba0e2cf9f67f9377cba257'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 53836,
                                    'sha256': 'f96f9bd0179d96a62d7e90c64b9c8b713d010ebda81088c539a917a83d851172'},
                    'WORKER_RESULT.json': {'bytes': 53720,
                                           'sha256': '35e5b2c76b05c53cc726c9cd12b0cb1dd660486a7a707346c7c1d2ed95771a12'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                                 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                                 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                                 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                     'failures': {'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': 'normal '
                                                                                     'failed/scope '
                                                                                     'differs: '
                                                                                     'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'},
                     'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                     'selected_live_source_count': 157,
                     'direct_import_readiness': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid']}}],
 'owners': {'ImbalancedChen.P5OriginalSharpPrimeSynthesis': {'accepting_run_index': 0,
                                                             'public_name': 'SYNTHESIS_AC_PUBLIC_ACCEPTANCE',
                                                             'audit_id': '2dd4c543e4398010981b',
                                                             'owned_count': 28,
                                                             'public_count': 28,
                                                             'source': {'bytes': 14462,
                                                                        'sha256': '990ceec9aae74a67c7e1b25e94d66b33644214e1fc0bb3193275ed1b09c50322'},
                                                             'audit_result': {'bytes': 19183,
                                                                              'sha256': 'bb8955fda37cfa3877e1e9b335bdc4db3d2e389582ca769fa7aa74786616a89b'},
                                                             'owner_live_source_closure_count': 112}},
 'extra_pins': {'/workspace/p1-complete-proof/20261126-p15-synthesis-api-repair-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 539949,
                                                                                                                                                                            'sha256': '1f0815dbb5409e66f4b890eed13a3ad3ebd919130c5544aee37adf3da3d50bbd'},
                '/workspace/blue-member-build/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.lean': {'bytes': 14601,
                                                                                                      'sha256': '82cfc7b75510076d0ded95130504639cde2ee39d38cff4133964a092d5cbcf54'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/ImbalancedChen.P5OriginalSingletonLowerTrimPaid/normal/ImbalancedChen.P5OriginalSingletonLowerTrimPaid/attempt-00000/normal-command.json': {'bytes': 1717,
                                                                                                                                                                                                                                                                       'sha256': '88cc4240dd5dec28e6afa6be29cf3f83c84e6ccc813888a72fa2b44a8f4673e7'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/ImbalancedChen.P5OriginalSingletonLowerTrimPaid/normal/ImbalancedChen.P5OriginalSingletonLowerTrimPaid/attempt-00000/normal.log': {'bytes': 190188,
                                                                                                                                                                                                                                                              'sha256': 'a6ea97ae5fde1d65ef1aee61394a4e4862cdde8dea6155e2358b6cbcc6059a7d'},
                '/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.setup.json': {'bytes': 6418102,
                                                                                                                           'sha256': '52a798bfd6ca48dbc188b265337d85a0cc50380481227a416514480adf048f2f'}},
 'failed_artifact_observations': {'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': {'.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.bc': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.bc.hash': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.c': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.c.hash': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.o': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.o.export': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.o.export.hash': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.o.hash': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.setup.json': {'bytes': 6418102,
                                                                                                                                                                    'sha256': '52a798bfd6ca48dbc188b265337d85a0cc50380481227a416514480adf048f2f'},
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.ilean': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.ilean.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.ir': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.ir.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.ir.sig': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.olean': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.olean.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.olean.private': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.olean.private.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.olean.server': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.olean.server.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.trace': None}},
 'current_read_live_source_count': 112,
 'current_read_preserved_dependency_count': 111}
CLAIMS = dict(normal_or_kernel_commands_executed=0, stock_readiness_executed_by_collector=False,
    types_or_archives_exported=False, axiom_union_exported=False, new_lean_acceptance=False,
    whole_P1_5_complete=False)
stage = 'require_frozen_actual_AC_evidence'


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
        need(record['source_commit'] == AC and record['published_source_count'] == 360 and
             all(record[k] == scope[k] for k in ('targets', 'accepted_owners', 'failures',
                 'reused_complete_selected_owners', 'selected_live_source_count')) and
             set(record['acceptance_bindings']) == set(accepted) and
             set(record['direct_import_readiness']) == set(scope['direct_import_readiness']) and
             all(record[k] is False for k in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not {'context_error', 'final_context_error', 'git_error'} & record.keys(), 'original AC scope differs')
    need(all(result.get(k) == v for k, v in worker.items()) and
         result['worker_exit_code'] == (0 if complete else 1) and
         result['all_selected_owners_accepted'] is complete, 'original AC terminal status differs')
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
                     runs[origins[module]][0]['acceptance_bindings'][module], 'same-AC reuse differs from first acceptance')
            else:
                need(module not in reused, 'reused owner lacks its original accepting run')
                origins[module] = index
    need(runs[0][0]['targets'] == [SYNTHESIS], 'Synthesis first-run target identity differs')
    return origins


def read_run(driver, s, graph, index, fixed):
    run = ROOT / AC / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py'] + [
        stem+'_'+side+'.json' for stem in ('CONTEXT', 'GIT') for side in ('BEFORE', 'AFTER')]
    files = {name: bind(run/name) for name in names}
    need(set(fixed['pins']) == set(names)-{'executed-driver.py'} and
         all(pin(files[name]) == wanted for name, wanted in fixed['pins'].items()) and
         pin(files['executed-driver.py']) == DRIVER_FP, 'original AC run pins differ')
    result, worker, context = [s.api.read_json(run/name) for name in
        ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
    complete = validate_scope(result, worker, fixed['scope'])
    for stem in ('CONTEXT', 'GIT'):
        need(pin(files[stem+'_BEFORE.json']) == pin(files[stem+'_AFTER.json']), 'original context/Git pair changed')
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == AC and context['committed_inputs']['source_anchor_commit'] == AB and
         driver.selection(requested) == requested and set(requested) == set(result['targets']) and
         s.d.compile_order([], requested, graph) == result['targets'], 'requested/executed AC scope differs')
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
    driver.require_completed_existing_owner(s, AC, spec, module, spec.initial_owners[module])
    binding = driver.acceptance_binding(s, AC, module)
    need(binding == runs[index][0]['acceptance_bindings'][module], 'live owner binding differs from original accepting run')
    folder = ROOT/AC/module
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
    return {'source_commit': AC, 'source_sha256': spec.sources[module], 'source': bind(source),
        'compiler_job': runs[index][2]['compiler_job'], 'original_accepting_run': runs[index][2]['original_run'],
        'audit_id': fixed['audit_id'], 'owned_count': counts[0], 'public_count': counts[1],
        'owner_live_source_closure_count': own_closure,
        'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
        'receipt_paths': {key: value['path'] for key, value in receipts.items()},
        'normal_kernel_full_owned_revalidated_without_execution': True,
        'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
        'receipt_rebound_to_current_commit': False, 'later_same_AC_reuse_run': later_reuse[0] if later_reuse else None}


def identity(spec, selected):
    return dict(source_commit=AC, source_anchor_commit=AB, driver={'commit': AC, 'path': DRIVER, **DRIVER_FP},
        source_manifest={'commit': AC, 'path': MANIFEST, **MANIFEST_FP}, published_source_count=len(spec.graph),
        selected_owners_revalidated=selected, current_read_live_source_count=len(spec.active),
        current_read_preserved_dependency_count=len(spec.dependency_pins))


def flat_summary(runs, index, module, owner, common):
    run = runs[index][2]; files = run['evidence_bindings']
    groups = {k: run[k] for k in ('accepted_owners', 'reused_complete_selected_owners', 'failed_modules',
        'not_accepted_modules', 'not_started_modules', 'worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    return {**common, **CLAIMS, 'schema': 'p15_AC_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_AC_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'compiler_job': run['compiler_job'],
        'original_run': 'runs/attempt-%05d' % index, 'original_result': pin(files['RESULT.json']),
        'original_worker_result': pin(files['WORKER_RESULT.json']), 'original_requested_targets': run['original_requested_targets'],
        'original_targets': run['targets'], **{'original_group_'+k: v for k, v in groups.items()},
        'original_group_live_closure_count': run['original_live_source_count'],
        'original_context_pairs': {stem: {side: pin(files[stem+'_'+side.upper()+'.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'], 'owners': {module: owner},
        'owner_live_source_closure_count': owner['owner_live_source_closure_count'],
        'later_same_source_reuse': runs[1][2] if owner['later_same_AC_reuse_run'] else None,
        'source_runtime_and_original_receipts_unchanged': True}


def collect():
    global stage
    need(__debug__, 'optimized Python refused')
    need(isinstance(PINNED, dict) and PINNED.get('schema') == 'p15_AC_fixed_actual_collection_inputs_v1',
         'actual AC later5 outcome and raw run/owner pins are not yet frozen')
    need(len(PINNED['runs']) == 2 and isinstance(PINNED['owners'], dict) and PINNED['owners'] and
         all(re.fullmatch('job_[0-9a-f]{32}', r['compiler_job']) for r in PINNED['runs']),
         'fixed actual runs/accepted-owner pins incomplete; no acceptance collection attempted')
    need(PINNED['runs'][0]['scope']['targets'] == [SYNTHESIS] and
         PINNED['runs'][0]['scope']['selected_live_source_count'] == 112 and
         PINNED['runs'][1]['scope']['selected_live_source_count'] == 157 and
         len(PINNED['runs'][1]['scope']['targets']) == 5 and
         PINNED['runs'][1]['scope']['targets'][0] == SYNTHESIS,
         'fixed AC first112/later5 source scope differs')
    # First process-environment access: unbound PINNED has already held.
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    stage = 'load_published_AC_reader'
    raw, manifest_raw = [subprocess.check_output(['git', 'show', AC+':'+path], cwd=REPO) for path in (DRIVER, MANIFEST)]
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published AC reader/manifest differs')
    executed = ROOT/AC/'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'original AC executed reader differs')
    driver = ModuleType('unchanged_AC_acceptance_reader'); driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, AB), 'AC reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    trees = {c: tree_inventory(ROOT/c) for c in (AC, AA, Y, W, U, S, Q)}
    extras = {p: file_fp(p) for p in PINNED['extra_pins']}
    need(extras == PINNED['extra_pins'], 'fixed extra evidence differs')
    for module, expected in PINNED['failed_artifact_observations'].items():
        need(set(expected) == set(driver.artifact_paths(module)) and driver.module_artifacts(s, module) == expected,
             'original failed owner artifact slots differ: '+module)
    manifest = json.loads(manifest_raw); graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    stage = 'read_two_original_AC_runs'
    runs = [read_run(driver, s, graph, i, fixed) for i, fixed in enumerate(PINNED['runs'])]
    need(runs[0][0]['targets'] == [SYNTHESIS] and
         runs[1][0]['targets'] == manifest['selection_guidance']['subsequent_5_targets'] and
         len(manifest['previously_accepted_targets']) == 13 and
         manifest['previously_accepted_targets'] == driver.PREVIOUSLY_ACCEPTED_TARGETS,
         'first/later target scopes or thirteen inherited prior identities differ')
    origins = accepting_runs(runs); selected = list(origins)
    need(set(origins) == set(PINNED['owners']) and all(PINNED['owners'][m]['accepting_run_index'] == i for m, i in origins.items()),
         'frozen owner accepting-run mapping differs')
    names = [PINNED['owners'][m]['public_name'] for m in selected]
    need(len(names) == len(set(names)) and all(re.fullmatch('[A-Za-z0-9_]+_AC_PUBLIC_ACCEPTANCE', n) for n in names),
         'owner public-summary names collide or differ')
    stage = 'original_AC_preflight_for_actual_accepted_prefix'
    spec = driver.preflight(s, AC, selected)
    need(len(spec.graph) == 360 and len(spec.active) == PINNED['current_read_live_source_count'] and
         len(spec.dependency_pins) == PINNED['current_read_preserved_dependency_count'] and
         spec.order == selected and set(spec.initial_owners) == set(selected), 'actual accepted-prefix read scope differs')
    for result, context, _ in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active-set(result['targets']), 'original AC context inventory differs')
    remaining_failed = {m for result, _, _ in runs for m in result['failures']} - set(origins)
    need(set(PINNED['failed_artifact_observations']) == remaining_failed,
         'remaining failed-owner artifact inventory is incomplete or stale')
    failure_observations = {}
    for module in sorted(remaining_failed):
        source = PROJECT/s.h.module_path(module)
        need(str(source) in extras and extras[str(source)] ==
             {k: manifest['project_sources'][module][k] for k in ('bytes', 'sha256')},
             'failed owner source is not pinned to the original AC source: '+module)
        normal_prefix = module+'/normal/'
        failure_observations[module] = {
            'source': bind(source), 'artifact_slots': PINNED['failed_artifact_observations'][module],
            'normal_evidence': {str(ROOT/AC/path): observed for path, observed in trees[AC].items()
                                if path.startswith(normal_prefix) and observed != 'directory'},
            'normal_receipt': str(ROOT/AC/module/'normal'/module/'NORMAL_PASS.json'),
            'normal_receipt_observation': trees[AC].get(module+'/normal/'+module+'/NORMAL_PASS.json'),
            'acceptance_claimed': False}
    artifacts = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    def target_sources():
        return {m: file_fp(PROJECT/s.h.module_path(m)) if os.path.lexists(PROJECT/s.h.module_path(m)) else None for m in driver.TARGETS}
    sources_before = target_sources()
    owners = {}
    for module, index in origins.items():
        stage = 'revalidate_original_AC_owner:'+module
        owners[module] = read_owner(driver, s, spec, runs, module, index, PINNED['owners'][module])
    stage = 'verify_read_only_preservation'
    need(driver.snapshot(s, spec) == spec.baseline and target_sources() == sources_before and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts and
         {p: file_fp(p) for p in extras} == extras and {c: tree_inventory(ROOT/c) for c in trees} == trees and
         s.d.original_git_state(REPO) == git_before, 'source/runtime/artifacts/original-evidence/Git changed during collection')
    common = identity(spec, selected)
    return {**common, **CLAIMS, 'schema': 'p15_AC_original_accepted_prefix_read_v1',
        'status': 'ORIGINAL_AC_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'collector': {'filename': Path(__file__).name, **file_fp(__file__)},
        'frozen_actual_input_binding': value_fp(PINNED),
        'public_summaries': {PINNED['owners'][m]['public_name']: flat_summary(runs, origins[m], m, row, common) for m, row in owners.items()},
        'original_runs': [r[2] for r in runs],
        'historical_owners_revalidated_in_current_read_scope': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'owned_count', 'public_count')} for m, row in spec.supplier_evidence.items()},
        'complete_original_AC_AA_Y_W_U_S_Q_evidence_inventory': {c: {'entry_count': len(t), **value_fp(t)} for c, t in trees.items()},
        'preserved_extra_evidence': extras, 'current_read_snapshot': value_fp(spec.baseline),
        'inherited_previous_target_count': 13,
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
