#!/usr/bin/env python3
"""Frozen read-only AA acceptance collector: original actual outcomes and evidence.

Uses unchanged AA preflight and original normal/kernel/full-owned readers after binding.
Mean keeps its first-run identity; subsequent owners keep their accepting run.
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
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
Z = 'bde4a91307cb5e5872b6fc3c1e4a1520908b10c2'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 251538, 'sha256': 'affa66215b9180e61052ba185f2502b5865416898bc8504b44175abe448bb074'}
MANIFEST_FP = {'bytes': 359729, 'sha256': '39eaeca8207c7f387d6b5c6e44d85b38836c721c3c7b1cf1172bbe4c7f95d6c3'}
# Frozen from actual AA metadata/results: Mean accepted at run0 and reused at run1;
# Synthesis failed in run1, four following owners unstarted, no later final stock.
PINNED = {'schema': 'p15_AA_fixed_actual_collection_inputs_v1',
 'runs': [{'compiler_job': 'job_a01a8d1e8a7d4178988c0c0a5f296b6d',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 300455,
                                           'sha256': '4ab18f4fe977dfef04b51c9138ee34a31a190030f4a45e265d25d000c81a13bc'},
                    'CONTEXT_BEFORE.json': {'bytes': 300455,
                                            'sha256': '4ab18f4fe977dfef04b51c9138ee34a31a190030f4a45e265d25d000c81a13bc'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 8391,
                                    'sha256': '6256690daae433327b6ef7543891ff829397bda1b15b92ae90096eb104bd9acb'},
                    'WORKER_RESULT.json': {'bytes': 8326,
                                           'sha256': '81e3d09172c6d6e4ba8fcb6af9979553c3b81cbcc22bff92c8b4774e838f2201'}},
           'scope': {'targets': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                     'accepted_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                     'failures': {},
                     'reused_complete_selected_owners': [],
                     'selected_live_source_count': 108,
                     'direct_import_readiness': ['ImbalancedChen.P5PrimeDivisorMeanCorrection']}},
          {'compiler_job': 'job_2d377894edb64660880d7f3e8783b2ee',
           'pins': {'CONTEXT_AFTER.json': {'bytes': 515448,
                                           'sha256': '257662bbd5d7c94ec64762a9956bbfd75e3e8f1e41a982f3439f4873041b901b'},
                    'CONTEXT_BEFORE.json': {'bytes': 515448,
                                            'sha256': '257662bbd5d7c94ec64762a9956bbfd75e3e8f1e41a982f3439f4873041b901b'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'RESULT.json': {'bytes': 52166,
                                    'sha256': 'cdc4c244088aaf3ca473a2d470c71bd303f72babb301246852e99ad6aa803230'},
                    'WORKER_RESULT.json': {'bytes': 52050,
                                           'sha256': '0bef1c288b0bfd2ee471667b383e09a1b1d6172946e2665b575753525cbf00c1'}},
           'scope': {'targets': ['ImbalancedChen.P5PrimeDivisorMeanCorrection',
                                 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                                 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                                 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                                 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
                     'accepted_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                     'failures': {'ImbalancedChen.P5OriginalSharpPrimeSynthesis': 'normal '
                                                                                  'failed/scope '
                                                                                  'differs: '
                                                                                  'ImbalancedChen.P5OriginalSharpPrimeSynthesis'},
                     'reused_complete_selected_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                     'selected_live_source_count': 157,
                     'direct_import_readiness': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis']}}],
 'owners': {'ImbalancedChen.P5PrimeDivisorMeanCorrection': {'accepting_run_index': 0,
                                                            'public_name': 'MEAN_AA_PUBLIC_ACCEPTANCE',
                                                            'audit_id': '6f3e2f324ba32c191175',
                                                            'owned_count': 22,
                                                            'public_count': 22,
                                                            'source': {'bytes': 17171,
                                                                       'sha256': 'efb2138a0a1837c60ab5484afee7d884364dbf118f2753a3690881baebb4c02d'},
                                                            'audit_result': {'bytes': 18683,
                                                                             'sha256': '66dfe12b9a4f4710ff268efa914caf31499fe093f09a6d90f45753a6be8ef911'},
                                                            'owner_live_source_closure_count': 108}},
 'extra_pins': {'/workspace/p1-complete-proof/20261126-p15-mean-api-repair-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 530642,
                                                                                                                                                                       'sha256': '32861aa7155d2e3f2e7a85bfed7d340759d2a0730784ef67134c24e21af8b363'},
                '/workspace/blue-member-build/ImbalancedChen/P5OriginalSharpPrimeSynthesis.lean': {'bytes': 14458,
                                                                                                   'sha256': '9d8b3b273ade3bf3a35aff7469e16f5fac24d9896eb31171c48c0f04328a8cd7'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/ImbalancedChen.P5OriginalSharpPrimeSynthesis/normal/ImbalancedChen.P5OriginalSharpPrimeSynthesis/attempt-00000/normal-command.json': {'bytes': 1125,
                                                                                                                                                                                                                                                                 'sha256': 'ebaf1b9204b7b43f01b9e6e4f2743068118e3c982d8a1ea0f86ca989c9a5a876'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/ImbalancedChen.P5OriginalSharpPrimeSynthesis/normal/ImbalancedChen.P5OriginalSharpPrimeSynthesis/attempt-00000/normal.log': {'bytes': 188154,
                                                                                                                                                                                                                                                        'sha256': '6ca572f41563749f9c2820e82fbb6e60003dc7c402d432596733c790e8292809'},
                '/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.setup.json': {'bytes': 6417017,
                                                                                                                        'sha256': '42acce65ed6a2b300809309fd909236cd4de13bfb9b5abe1cf27baac10dca87e'}},
 'failed_artifact_observations': {'ImbalancedChen.P5OriginalSharpPrimeSynthesis': {'.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.bc': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.bc.hash': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.c': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.c.hash': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.o': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.o.export': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.o.export.hash': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.o.hash': None,
                                                                                   '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.setup.json': {'bytes': 6417017,
                                                                                                                                                              'sha256': '42acce65ed6a2b300809309fd909236cd4de13bfb9b5abe1cf27baac10dca87e'},
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.ilean': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.ilean.hash': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.ir': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.ir.hash': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.ir.sig': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.olean': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.olean.hash': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.olean.private': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.olean.private.hash': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.olean.server': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.olean.server.hash': None,
                                                                                   '.lake/build/lib/lean/ImbalancedChen/P5OriginalSharpPrimeSynthesis.trace': None}},
 'current_read_live_source_count': 108,
 'current_read_preserved_dependency_count': 107}
CLAIMS = dict(normal_or_kernel_commands_executed=0, stock_readiness_executed_by_collector=False,
    types_or_archives_exported=False, axiom_union_exported=False, new_lean_acceptance=False,
    whole_P1_5_complete=False)
stage = 'require_frozen_actual_AA_evidence'


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
        need(record['source_commit'] == AA and record['published_source_count'] == 360 and
             all(record[k] == scope[k] for k in ('targets', 'accepted_owners', 'failures',
                 'reused_complete_selected_owners', 'selected_live_source_count')) and
             set(record['acceptance_bindings']) == set(accepted) and
             set(record['direct_import_readiness']) == set(scope['direct_import_readiness']) and
             all(record[k] is False for k in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not {'context_error', 'final_context_error', 'git_error'} & record.keys(), 'original AA scope differs')
    need(all(result.get(k) == v for k, v in worker.items()) and
         result['worker_exit_code'] == (0 if complete else 1) and
         result['all_selected_owners_accepted'] is complete, 'original AA terminal status differs')
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
                     runs[origins[module]][0]['acceptance_bindings'][module], 'same-AA reuse differs from first acceptance')
            else:
                need(module not in reused, 'reused owner lacks its original accepting run')
                origins[module] = index
    need(runs[0][0]['targets'] == [MEAN], 'Mean first-run target identity differs')
    return origins


def read_run(driver, s, graph, index, fixed):
    run = ROOT / AA / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py'] + [
        stem+'_'+side+'.json' for stem in ('CONTEXT', 'GIT') for side in ('BEFORE', 'AFTER')]
    files = {name: bind(run/name) for name in names}
    need(set(fixed['pins']) == set(names)-{'executed-driver.py'} and
         all(pin(files[name]) == wanted for name, wanted in fixed['pins'].items()) and
         pin(files['executed-driver.py']) == DRIVER_FP, 'original AA run pins differ')
    result, worker, context = [s.api.read_json(run/name) for name in
        ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
    complete = validate_scope(result, worker, fixed['scope'])
    for stem in ('CONTEXT', 'GIT'):
        need(pin(files[stem+'_BEFORE.json']) == pin(files[stem+'_AFTER.json']), 'original context/Git pair changed')
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == AA and context['committed_inputs']['source_anchor_commit'] == Z and
         driver.selection(requested) == requested and set(requested) == set(result['targets']) and
         s.d.compile_order([], requested, graph) == result['targets'], 'requested/executed AA scope differs')
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
    driver.require_completed_existing_owner(s, AA, spec, module, spec.initial_owners[module])
    binding = driver.acceptance_binding(s, AA, module)
    need(binding == runs[index][0]['acceptance_bindings'][module], 'live owner binding differs from original accepting run')
    folder = ROOT/AA/module
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
    return {'source_commit': AA, 'source_sha256': spec.sources[module], 'source': bind(source),
        'compiler_job': runs[index][2]['compiler_job'], 'original_accepting_run': runs[index][2]['original_run'],
        'audit_id': fixed['audit_id'], 'owned_count': counts[0], 'public_count': counts[1],
        'owner_live_source_closure_count': own_closure,
        'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
        'receipt_paths': {key: value['path'] for key, value in receipts.items()},
        'normal_kernel_full_owned_revalidated_without_execution': True,
        'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
        'receipt_rebound_to_current_commit': False, 'later_same_AA_reuse_run': later_reuse[0] if later_reuse else None}


def identity(spec, selected):
    return dict(source_commit=AA, source_anchor_commit=Z, driver={'commit': AA, 'path': DRIVER, **DRIVER_FP},
        source_manifest={'commit': AA, 'path': MANIFEST, **MANIFEST_FP}, published_source_count=len(spec.graph),
        selected_owners_revalidated=selected, current_read_live_source_count=len(spec.active),
        current_read_preserved_dependency_count=len(spec.dependency_pins))


def flat_summary(runs, index, module, owner, common):
    run = runs[index][2]; files = run['evidence_bindings']
    groups = {k: run[k] for k in ('accepted_owners', 'reused_complete_selected_owners', 'failed_modules',
        'not_accepted_modules', 'not_started_modules', 'worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    return {**common, **CLAIMS, 'schema': 'p15_AA_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_AA_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'compiler_job': run['compiler_job'],
        'original_run': 'runs/attempt-%05d' % index, 'original_result': pin(files['RESULT.json']),
        'original_worker_result': pin(files['WORKER_RESULT.json']), 'original_requested_targets': run['original_requested_targets'],
        'original_targets': run['targets'], **{'original_group_'+k: v for k, v in groups.items()},
        'original_group_live_closure_count': run['original_live_source_count'],
        'original_context_pairs': {stem: {side: pin(files[stem+'_'+side.upper()+'.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'], 'owners': {module: owner},
        'owner_live_source_closure_count': owner['owner_live_source_closure_count'],
        'later_same_source_reuse': runs[1][2] if owner['later_same_AA_reuse_run'] else None,
        'source_runtime_and_original_receipts_unchanged': True}


def collect():
    global stage
    need(__debug__, 'optimized Python refused')
    need(isinstance(PINNED, dict) and PINNED.get('schema') == 'p15_AA_fixed_actual_collection_inputs_v1',
         'actual AA later6 outcome and raw run/owner pins are not yet frozen')
    need(len(PINNED['runs']) == 2 and isinstance(PINNED['owners'], dict) and PINNED['owners'] and
         all(re.fullmatch('job_[0-9a-f]{32}', r['compiler_job']) for r in PINNED['runs']),
         'fixed actual runs/accepted-owner pins incomplete; no acceptance collection attempted')
    need(PINNED['runs'][0]['scope']['targets'] == [MEAN] and
         PINNED['runs'][0]['scope']['selected_live_source_count'] == 108 and
         PINNED['runs'][1]['scope']['selected_live_source_count'] == 157 and
         len(PINNED['runs'][1]['scope']['targets']) == 6 and
         PINNED['runs'][1]['scope']['targets'][0] == MEAN,
         'fixed AA first108/later6 source scope differs')
    # First process-environment access: unbound PINNED has already held.
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    stage = 'load_published_AA_reader'
    raw, manifest_raw = [subprocess.check_output(['git', 'show', AA+':'+path], cwd=REPO) for path in (DRIVER, MANIFEST)]
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published AA reader/manifest differs')
    executed = ROOT/AA/'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'original AA executed reader differs')
    driver = ModuleType('unchanged_AA_acceptance_reader'); driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, Z), 'AA reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    trees = {c: tree_inventory(ROOT/c) for c in (AA, Y, W, U, S, Q)}
    extras = {p: file_fp(p) for p in PINNED['extra_pins']}
    need(extras == PINNED['extra_pins'], 'fixed extra evidence differs')
    for module, expected in PINNED['failed_artifact_observations'].items():
        need(set(expected) == set(driver.artifact_paths(module)) and driver.module_artifacts(s, module) == expected,
             'original failed owner artifact slots differ: '+module)
    manifest = json.loads(manifest_raw); graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    stage = 'read_two_original_AA_runs'
    runs = [read_run(driver, s, graph, i, fixed) for i, fixed in enumerate(PINNED['runs'])]
    need(runs[0][0]['targets'] == [MEAN] and
         runs[1][0]['targets'] == manifest['selection_guidance']['subsequent_6_targets'] and
         len(manifest['previously_accepted_targets']) == 12 and
         manifest['previously_accepted_targets'] == driver.PREVIOUSLY_ACCEPTED_TARGETS,
         'first/later target scopes or twelve inherited prior identities differ')
    origins = accepting_runs(runs); selected = list(origins)
    need(set(origins) == set(PINNED['owners']) and all(PINNED['owners'][m]['accepting_run_index'] == i for m, i in origins.items()),
         'frozen owner accepting-run mapping differs')
    names = [PINNED['owners'][m]['public_name'] for m in selected]
    need(len(names) == len(set(names)) and all(re.fullmatch('[A-Za-z0-9_]+_AA_PUBLIC_ACCEPTANCE', n) for n in names),
         'owner public-summary names collide or differ')
    stage = 'original_AA_preflight_for_actual_accepted_prefix'
    spec = driver.preflight(s, AA, selected)
    need(len(spec.graph) == 360 and len(spec.active) == PINNED['current_read_live_source_count'] and
         len(spec.dependency_pins) == PINNED['current_read_preserved_dependency_count'] and
         spec.order == selected and set(spec.initial_owners) == set(selected), 'actual accepted-prefix read scope differs')
    for result, context, _ in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active-set(result['targets']), 'original AA context inventory differs')
    remaining_failed = {m for result, _, _ in runs for m in result['failures']} - set(origins)
    need(set(PINNED['failed_artifact_observations']) == remaining_failed,
         'remaining failed-owner artifact inventory is incomplete or stale')
    failure_observations = {}
    for module in sorted(remaining_failed):
        source = PROJECT/s.h.module_path(module)
        need(str(source) in extras and extras[str(source)] ==
             {k: manifest['project_sources'][module][k] for k in ('bytes', 'sha256')},
             'failed owner source is not pinned to the original AA source: '+module)
        normal_prefix = module+'/normal/'
        failure_observations[module] = {
            'source': bind(source), 'artifact_slots': PINNED['failed_artifact_observations'][module],
            'normal_evidence': {str(ROOT/AA/path): observed for path, observed in trees[AA].items()
                                if path.startswith(normal_prefix) and observed != 'directory'},
            'normal_receipt': str(ROOT/AA/module/'normal'/module/'NORMAL_PASS.json'),
            'normal_receipt_observation': trees[AA].get(module+'/normal/'+module+'/NORMAL_PASS.json'),
            'acceptance_claimed': False}
    artifacts = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    def target_sources():
        return {m: file_fp(PROJECT/s.h.module_path(m)) if os.path.lexists(PROJECT/s.h.module_path(m)) else None for m in driver.TARGETS}
    sources_before = target_sources()
    owners = {}
    for module, index in origins.items():
        stage = 'revalidate_original_AA_owner:'+module
        owners[module] = read_owner(driver, s, spec, runs, module, index, PINNED['owners'][module])
    stage = 'verify_read_only_preservation'
    need(driver.snapshot(s, spec) == spec.baseline and target_sources() == sources_before and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts and
         {p: file_fp(p) for p in extras} == extras and {c: tree_inventory(ROOT/c) for c in trees} == trees and
         s.d.original_git_state(REPO) == git_before, 'source/runtime/artifacts/original-evidence/Git changed during collection')
    common = identity(spec, selected)
    return {**common, **CLAIMS, 'schema': 'p15_AA_original_accepted_prefix_read_v1',
        'status': 'ORIGINAL_AA_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'collector': {'filename': Path(__file__).name, **file_fp(__file__)},
        'frozen_actual_input_binding': value_fp(PINNED),
        'public_summaries': {PINNED['owners'][m]['public_name']: flat_summary(runs, origins[m], m, row, common) for m, row in owners.items()},
        'original_runs': [r[2] for r in runs],
        'historical_owners_revalidated_in_current_read_scope': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'owned_count', 'public_count')} for m, row in spec.supplier_evidence.items()},
        'complete_original_AA_Y_W_U_S_Q_evidence_inventory': {c: {'entry_count': len(t), **value_fp(t)} for c, t in trees.items()},
        'preserved_extra_evidence': extras, 'current_read_snapshot': value_fp(spec.baseline),
        'inherited_previous_target_count': 12,
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
