#!/usr/bin/env python3
"""Read the two fixed actual U runs and revalidate their accepted owners.

Uses the unchanged U preflight and original normal/kernel/full-owned readers.
Word keeps its first-run identity; subsequent owners keep their accepting run.
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
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
T = '999510c460e6e026c8cabe46c5f35876f7201f8e'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 152370, 'sha256': '9d9c2e467b3fd6271b7b0101812094ca6ff768f1ea831812b6de4c95a0dd9c7a'}
MANIFEST_FP = {'bytes': 349643, 'sha256': 'ae3f6bb915e0ed2dc799fd6bfed2b906aab3efac3df9186c9c1d54da4b53a1af'}
# Frozen from ACTUAL_U_METADATA.json; later10 stopped at SmoothLicence after Word and AllGroup.
PINNED = {'schema': 'p15_U_fixed_actual_collection_inputs_v1',
 'runs': [{'compiler_job': 'job_9eeb0db5123a4283ad6a18864bdc342b',
           'pins': {'RESULT.json': {'bytes': 40734,
                                    'sha256': '2e35df4747d247f46509520b5c749e06c8c55156433d8343a1c784e7f4d90ee1'},
                    'WORKER_RESULT.json': {'bytes': 40669,
                                           'sha256': 'a30618e83784765df9b6522f36d6193356c7d03c694ff94baf82595777c8cffb'},
                    'CONTEXT_BEFORE.json': {'bytes': 271784,
                                            'sha256': '7022d734b1650644e56e48e06563ea5b04cb2d08accb53170d9af06ac25dcbb3'},
                    'CONTEXT_AFTER.json': {'bytes': 271784,
                                           'sha256': '7022d734b1650644e56e48e06563ea5b04cb2d08accb53170d9af06ac25dcbb3'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}},
           'scope': {'targets': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary'],
                     'accepted_owners': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary'],
                     'failures': {},
                     'reused_complete_selected_owners': [],
                     'selected_live_source_count': 77,
                     'direct_import_readiness': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary']}},
          {'compiler_job': 'job_78ea387bf32d4c57b60346dcf7451e50',
           'pins': {'RESULT.json': {'bytes': 52560,
                                    'sha256': '02c712e2179b51dd6ba1e73ca3398250ed7070f14714b5312365c29b20386af3'},
                    'WORKER_RESULT.json': {'bytes': 52444,
                                           'sha256': 'f21cfc35c5796567e4a229561bb46dc3350ee3f8c60335583cf7f28c001f8317'},
                    'CONTEXT_BEFORE.json': {'bytes': 483194,
                                            'sha256': '5721f6257fe6090b63584ebb1bfa496e6c5822eb09bd529a3ffba0a4e35f1e20'},
                    'CONTEXT_AFTER.json': {'bytes': 483194,
                                           'sha256': '5721f6257fe6090b63584ebb1bfa496e6c5822eb09bd529a3ffba0a4e35f1e20'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}},
           'scope': {'targets': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
                                 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
                                 'ImbalancedChen.P1OriginalSingletonSmoothLicence',
                                 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
                                 'ImbalancedChen.P5PrimeDivisorMeanCorrection',
                                 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                                 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                                 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                                 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
                     'accepted_owners': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
                                         'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy'],
                     'failures': {'ImbalancedChen.P1OriginalSingletonSmoothLicence': 'normal failed/scope '
                                                                                     'differs: '
                                                                                     'ImbalancedChen.P1OriginalSingletonSmoothLicence'},
                     'reused_complete_selected_owners': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary'],
                     'selected_live_source_count': 157,
                     'direct_import_readiness': ['ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
                                                 'ImbalancedChen.P1OriginalSingletonSmoothLicence']}}],
 'owners': {'ImbalancedChen.P5IndependentPrimeSourceWordDictionary': {'accepting_run_index': 0,
                                                                      'public_name': 'WORD_U_PUBLIC_ACCEPTANCE',
                                                                      'audit_id': 'bac21ef05eaf61163bfc',
                                                                      'owned_count': 15,
                                                                      'public_count': 15,
                                                                      'source': {'bytes': 5672,
                                                                                 'sha256': '021c39e9439f5e304e752093a332f66e68902b1a42a697c5ad4eda2ee29f648f'},
                                                                      'audit_result': {'bytes': 15601,
                                                                                       'sha256': 'c5557204ebcdeae831e919a2973cea7ebf864b8d06809e30399101e39ede9f59'},
                                                                      'owner_live_source_closure_count': 77},
            'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy': {'accepting_run_index': 1,
                                                                    'public_name': 'ALLGROUP_U_PUBLIC_ACCEPTANCE',
                                                                    'audit_id': '7beec90b0fdc63aaa2de',
                                                                    'owned_count': 15,
                                                                    'public_count': 15,
                                                                    'source': {'bytes': 9345,
                                                                               'sha256': '089dac23d8ce96fde4f5fcb129c3b525955a919d7665937821a5ee31d11ab8be'},
                                                                    'audit_result': {'bytes': 22656,
                                                                                     'sha256': '41e4471029f44f0961c3edaf87f415e8142ac628ccf2dd42a126ad7f3468ddbf'},
                                                                    'owner_live_source_closure_count': 139}},
 'extra_pins': {'/workspace/p1-complete-proof/20261126-p15-word-api-repair-v1/2779eb7b2b0433bea10d523ef976317893f8429d/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 497566,
                                                                                                                                                                       'sha256': 'c55080bf18d46c0612ef805a8b1c5915fbb65cadbcc6763f683598e69b579e47'},
                '/workspace/blue-member-build/ImbalancedChen/P1OriginalSingletonSmoothLicence.lean': {'bytes': 4358,
                                                                                                      'sha256': 'f74c3c51c0b1de7b493f9fe7e883d89a4b5c163624bb5be1f6901fbec3424011'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/2779eb7b2b0433bea10d523ef976317893f8429d/ImbalancedChen.P1OriginalSingletonSmoothLicence/normal/ImbalancedChen.P1OriginalSingletonSmoothLicence/attempt-00000/normal-command.json': {'bytes': 1773,
                                                                                                                                                                                                                                                                       'sha256': '12b107fffdd1aa29c0aa492e1ae66ada2142eddc00bc955a5ecf29f5eff4e6c3'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/2779eb7b2b0433bea10d523ef976317893f8429d/ImbalancedChen.P1OriginalSingletonSmoothLicence/normal/ImbalancedChen.P1OriginalSingletonSmoothLicence/attempt-00000/normal.log': {'bytes': 190008,
                                                                                                                                                                                                                                                              'sha256': 'ead8ded3a2de4f4bd9da374cfa4932228ee2986b88cd85428f3583e0a332dd0b'},
                '/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.setup.json': {'bytes': 6423922,
                                                                                                                           'sha256': '963197a94a0370d47ee383bb103770b7af29e692df06b8195d72906e1cc0fff7'}},
 'failed_artifact_observations': {'ImbalancedChen.P1OriginalSingletonSmoothLicence': {'.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.c': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.c.hash': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.setup.json': {'bytes': 6423922,
                                                                                                                                                                    'sha256': '963197a94a0370d47ee383bb103770b7af29e692df06b8195d72906e1cc0fff7'},
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.bc': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.bc.hash': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.o': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.o.hash': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.o.export': None,
                                                                                      '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.o.export.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.olean': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.olean.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.olean.private': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.olean.private.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.olean.server': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.olean.server.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.ilean': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.ilean.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.trace': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.ir': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.ir.hash': None,
                                                                                      '.lake/build/lib/lean/ImbalancedChen/P1OriginalSingletonSmoothLicence.ir.sig': None}},
 'current_read_live_source_count': 139,
 'current_read_preserved_dependency_count': 137}
CLAIMS = dict(normal_or_kernel_commands_executed=0, stock_readiness_executed_by_collector=False,
    types_or_archives_exported=False, axiom_union_exported=False, new_lean_acceptance=False,
    whole_P1_5_complete=False)
stage = 'require_frozen_actual_U_evidence'


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
        need(record['source_commit'] == U and record['published_source_count'] == 360 and
             all(record[k] == scope[k] for k in ('targets', 'accepted_owners', 'failures',
                 'reused_complete_selected_owners', 'selected_live_source_count')) and
             set(record['acceptance_bindings']) == set(accepted) and
             set(record['direct_import_readiness']) == set(scope['direct_import_readiness']) and
             all(record[k] is False for k in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not {'context_error', 'final_context_error', 'git_error'} & record.keys(), 'original U scope differs')
    need(all(result.get(k) == v for k, v in worker.items()) and
         result['worker_exit_code'] == (0 if complete else 1) and
         result['all_selected_owners_accepted'] is complete, 'original U terminal status differs')
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
                     runs[origins[module]][0]['acceptance_bindings'][module], 'same-U reuse differs from first acceptance')
            else:
                need(module not in reused, 'reused owner lacks its original accepting run')
                origins[module] = index
    need(origins.get(WORD) == 0 and runs[0][0]['accepted_owners'] == [WORD], 'Word first-run identity differs')
    return origins


def read_run(driver, s, graph, index, fixed):
    run = ROOT / U / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py'] + [
        stem+'_'+side+'.json' for stem in ('CONTEXT', 'GIT') for side in ('BEFORE', 'AFTER')]
    files = {name: bind(run/name) for name in names}
    need(set(fixed['pins']) == set(names)-{'executed-driver.py'} and
         all(pin(files[name]) == wanted for name, wanted in fixed['pins'].items()) and
         pin(files['executed-driver.py']) == DRIVER_FP, 'original U run pins differ')
    result, worker, context = [s.api.read_json(run/name) for name in
        ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
    complete = validate_scope(result, worker, fixed['scope'])
    for stem in ('CONTEXT', 'GIT'):
        need(pin(files[stem+'_BEFORE.json']) == pin(files[stem+'_AFTER.json']), 'original context/Git pair changed')
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == U and context['committed_inputs']['source_anchor_commit'] == T and
         driver.selection(requested) == requested and set(requested) == set(result['targets']) and
         s.d.compile_order([], requested, graph) == result['targets'], 'requested/executed U scope differs')
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
    driver.require_completed_existing_owner(s, U, spec, module, spec.initial_owners[module])
    binding = driver.acceptance_binding(s, U, module)
    need(binding == runs[index][0]['acceptance_bindings'][module], 'live owner binding differs from original accepting run')
    folder = ROOT/U/module
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
    return {'source_commit': U, 'source_sha256': spec.sources[module], 'source': bind(source),
        'compiler_job': runs[index][2]['compiler_job'], 'original_accepting_run': runs[index][2]['original_run'],
        'audit_id': fixed['audit_id'], 'owned_count': counts[0], 'public_count': counts[1],
        'owner_live_source_closure_count': own_closure,
        'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
        'receipt_paths': {key: value['path'] for key, value in receipts.items()},
        'normal_kernel_full_owned_revalidated_without_execution': True,
        'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
        'receipt_rebound_to_current_commit': False, 'later_same_U_reuse_run': later_reuse[0] if later_reuse else None}


def identity(spec, selected):
    return dict(source_commit=U, source_anchor_commit=T, driver={'commit': U, 'path': DRIVER, **DRIVER_FP},
        source_manifest={'commit': U, 'path': MANIFEST, **MANIFEST_FP}, published_source_count=len(spec.graph),
        selected_owners_revalidated=selected, current_read_live_source_count=len(spec.active),
        current_read_preserved_dependency_count=len(spec.dependency_pins))


def flat_summary(runs, index, module, owner, common):
    run = runs[index][2]; files = run['evidence_bindings']
    groups = {k: run[k] for k in ('accepted_owners', 'reused_complete_selected_owners', 'failed_modules',
        'not_accepted_modules', 'not_started_modules', 'worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    return {**common, **CLAIMS, 'schema': 'p15_U_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_U_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'compiler_job': run['compiler_job'],
        'original_run': 'runs/attempt-%05d' % index, 'original_result': pin(files['RESULT.json']),
        'original_worker_result': pin(files['WORKER_RESULT.json']), 'original_requested_targets': run['original_requested_targets'],
        'original_targets': run['targets'], **{'original_group_'+k: v for k, v in groups.items()},
        'original_group_live_closure_count': run['original_live_source_count'],
        'original_context_pairs': {stem: {side: pin(files[stem+'_'+side.upper()+'.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'], 'owners': {module: owner},
        'owner_live_source_closure_count': owner['owner_live_source_closure_count'],
        'later_same_source_reuse': runs[1][2] if owner['later_same_U_reuse_run'] else None,
        'source_runtime_and_original_receipts_unchanged': True}


def collect():
    global stage
    need(__debug__, 'optimized Python refused')
    need(isinstance(PINNED, dict) and PINNED.get('schema') == 'p15_U_fixed_actual_collection_inputs_v1',
         'actual U later10 outcome and raw run/owner pins are not yet frozen')
    need(len(PINNED['runs']) == 2 and PINNED['owners'] and
         all(re.fullmatch('job_[0-9a-f]{32}', r['compiler_job']) for r in PINNED['runs']), 'fixed actual input identity incomplete')
    stage = 'load_published_U_reader'
    raw, manifest_raw = [subprocess.check_output(['git', 'show', U+':'+path], cwd=REPO) for path in (DRIVER, MANIFEST)]
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published U reader/manifest differs')
    executed = ROOT/U/'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'original U executed reader differs')
    driver = ModuleType('unchanged_U_acceptance_reader'); driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, T), 'U reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    trees = {c: tree_inventory(ROOT/c) for c in (U, S, Q)}
    extras = {p: file_fp(p) for p in PINNED['extra_pins']}
    need(extras == PINNED['extra_pins'], 'fixed extra evidence differs')
    for module, expected in PINNED['failed_artifact_observations'].items():
        need(set(expected) == set(driver.artifact_paths(module)) and driver.module_artifacts(s, module) == expected,
             'original failed owner artifact slots differ: '+module)
    manifest = json.loads(manifest_raw); graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    stage = 'read_two_original_U_runs'
    runs = [read_run(driver, s, graph, i, fixed) for i, fixed in enumerate(PINNED['runs'])]
    need(runs[0][0]['targets'] == [WORD] and runs[0][0]['all_selected_owners_accepted'] is True and
         set(runs[1][0]['targets']) == set(manifest['selection_guidance']['subsequent_10_targets']), 'first/later target scopes differ')
    origins = accepting_runs(runs); selected = list(origins)
    need(set(origins) == set(PINNED['owners']) and all(PINNED['owners'][m]['accepting_run_index'] == i for m, i in origins.items()),
         'frozen owner accepting-run mapping differs')
    names = [PINNED['owners'][m]['public_name'] for m in selected]
    need(len(names) == len(set(names)) and all(re.fullmatch('[A-Za-z0-9_]+_U_PUBLIC_ACCEPTANCE', n) for n in names),
         'owner public-summary names collide or differ')
    stage = 'original_U_preflight_for_actual_accepted_prefix'
    spec = driver.preflight(s, U, selected)
    need(len(spec.graph) == 360 and len(spec.active) == PINNED['current_read_live_source_count'] and
         len(spec.dependency_pins) == PINNED['current_read_preserved_dependency_count'] and
         spec.order == selected and set(spec.initial_owners) == set(selected), 'actual accepted-prefix read scope differs')
    for result, context, _ in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active-set(result['targets']), 'original U context inventory differs')
    artifacts = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    def target_sources():
        return {m: file_fp(PROJECT/s.h.module_path(m)) if os.path.lexists(PROJECT/s.h.module_path(m)) else None for m in driver.TARGETS}
    sources_before = target_sources()
    owners = {}
    for module, index in origins.items():
        stage = 'revalidate_original_U_owner:'+module
        owners[module] = read_owner(driver, s, spec, runs, module, index, PINNED['owners'][module])
    stage = 'verify_read_only_preservation'
    need(driver.snapshot(s, spec) == spec.baseline and target_sources() == sources_before and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts and
         {p: file_fp(p) for p in extras} == extras and {c: tree_inventory(ROOT/c) for c in trees} == trees and
         s.d.original_git_state(REPO) == git_before, 'source/runtime/artifacts/original-evidence/Git changed during collection')
    common = identity(spec, selected)
    return {**common, **CLAIMS, 'schema': 'p15_U_original_accepted_prefix_read_v1',
        'status': 'ORIGINAL_U_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'collector': {'filename': Path(__file__).name, **file_fp(__file__)},
        'frozen_actual_input_binding': value_fp(PINNED),
        'public_summaries': {PINNED['owners'][m]['public_name']: flat_summary(runs, origins[m], m, row, common) for m, row in owners.items()},
        'original_runs': [r[2] for r in runs],
        'historical_owners_revalidated_in_current_read_scope': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'owned_count', 'public_count')} for m, row in spec.supplier_evidence.items()},
        'complete_original_U_S_Q_evidence_inventory': {c: {'entry_count': len(t), **value_fp(t)} for c, t in trees.items()},
        'preserved_extra_evidence': extras, 'current_read_snapshot': value_fp(spec.baseline),
        'current_dirty_Git_state': value_fp(git_before), 'all_current_target_artifact_slots_watched': len(driver.TARGETS)*21,
        'all_current_target_source_slots_watched': len(sources_before), 'current_target_source_inventory': value_fp(sources_before),
        'remaining_failed_modules': runs[1][2]['failed_modules'], 'remaining_not_started_modules': runs[1][2]['not_started_modules'],
        'source_runtime_artifacts_and_original_receipts_unchanged': True, 'current_dirty_Git_state_unchanged': True}


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
