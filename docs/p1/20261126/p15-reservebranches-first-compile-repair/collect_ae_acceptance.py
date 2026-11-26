#!/usr/bin/env python3
"""Frozen actual AE read-only acceptance collector.

LowerTrim remains accepted by original run0; AtlasTrim remains accepted by partial run1.
Original run1 reuses LowerTrim, fails ReserveBranches, and leaves RoughPrime unstarted.
Uses unchanged AE readers; no compiler, stock query, installer, archive, or Git mutation.
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
# Actual AE publication and original run/owner outcome pins are frozen.
AE = 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 306454, 'sha256': '2fac63da6dd93b54ded3a8c5c8542558f3a03a738092fcb43b2336ab8674705e'}
MANIFEST_FP = {'bytes': 364863, 'sha256': '6c5c0b8795a2c6fa1265e5030b12a9e77500efe651b8796b11b748a0ed47ada5'}
# Frozen from actual AE RESULT/WORKER byte pins and ACTUAL_AE_METADATA.json.
# LowerTrim 10/10 and AtlasTrim 11/9 retain different original accepting runs.
PINNED = {'schema': 'p15_AE_fixed_actual_collection_inputs_v1',
 'runs': [{'compiler_job': 'job_d3c60cd1867242fab3195258062e2290',
           'pins': {'RESULT.json': {'bytes': 13666,
                                    'sha256': 'b15f809241e1a6d9e47294ca4b92fcea0ed77a16c7e2da1b9396926ca9491243'},
                    'WORKER_RESULT.json': {'bytes': 13601,
                                           'sha256': '918fb5a375a6624c792a6fbe573250f3daa414da8f52eabdcd17e855b6cb9f4a'},
                    'CONTEXT_BEFORE.json': {'bytes': 350763,
                                            'sha256': '9d74828ab53a3ad56d011c8d0b50e9cf6634be33bcb937979f41282c20aaba6c'},
                    'CONTEXT_AFTER.json': {'bytes': 350763,
                                           'sha256': '9d74828ab53a3ad56d011c8d0b50e9cf6634be33bcb937979f41282c20aaba6c'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid'],
                     'failures': {},
                     'reused_complete_selected_owners': [],
                     'selected_live_source_count': 119,
                     'direct_import_readiness': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid']}},
          {'compiler_job': 'job_698d39e25f9d4800a912dc27a0bfe84b',
           'pins': {'RESULT.json': {'bytes': 62238,
                                    'sha256': '62f3e218a0eb3266eb06327692e4b5f1a86e236c51ca9b2957b688cd29e4a460'},
                    'WORKER_RESULT.json': {'bytes': 62122,
                                           'sha256': '933a47c3c87403b85b7506425406cb9878f2aa9334c5d9151b808701323fe8c5'},
                    'CONTEXT_BEFORE.json': {'bytes': 533346,
                                            'sha256': '0d8d8eb6b587dafa0f8af6d7cf113af19bae6860cef16e64b5095c9408f5ff63'},
                    'CONTEXT_AFTER.json': {'bytes': 533346,
                                           'sha256': '0d8d8eb6b587dafa0f8af6d7cf113af19bae6860cef16e64b5095c9408f5ff63'},
                    'GIT_BEFORE.json': {'bytes': 1157,
                                        'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                    'GIT_AFTER.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}},
           'scope': {'targets': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                                 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                                 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
                     'accepted_owners': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                                         'ImbalancedChen.P1OriginalSingletonAtlasTrim'],
                     'failures': {'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': 'normal '
                                                                                        'failed/scope '
                                                                                        'differs: '
                                                                                        'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'},
                     'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid'],
                     'selected_live_source_count': 157,
                     'direct_import_readiness': ['ImbalancedChen.P1OriginalSingletonAtlasTrim',
                                                 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches']}}],
 'owners': {'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': {'accepting_run_index': 0,
                                                                'public_name': 'LOWERTRIM_AE_PUBLIC_ACCEPTANCE',
                                                                'audit_id': 'e45153f0bb3e3268967a',
                                                                'owned_count': 10,
                                                                'public_count': 10,
                                                                'source': {'bytes': 14655,
                                                                           'sha256': 'f26884610a2d205368b347ed5fd80947c91c5973a6750bc0b333cb57dcb42106'},
                                                                'audit_result': {'bytes': 20073,
                                                                                 'sha256': '612ddebab56929f4bf5cede507507bb300043387d3c379f18780ee92514692fd'},
                                                                'owner_live_source_closure_count': 119},
            'ImbalancedChen.P1OriginalSingletonAtlasTrim': {'accepting_run_index': 1,
                                                            'public_name': 'ATLASTRIM_AE_PUBLIC_ACCEPTANCE',
                                                            'audit_id': '25adbe91b10ca6f615bb',
                                                            'owned_count': 11,
                                                            'public_count': 9,
                                                            'source': {'bytes': 8493,
                                                                       'sha256': '82d283e23ed857c134b9bd628a6711c24df8432796f55d7fb2a1a2a16d9f252a'},
                                                            'audit_result': {'bytes': 24143,
                                                                             'sha256': 'b7cc0a33feb0c750fcb38331bd3f89eaa74a0bf88c459485fc31e74a84fd66fb'},
                                                            'owner_live_source_closure_count': 153}},
 'extra_pins': {'/workspace/p1-complete-proof/20261126-p15-mean-api-repair-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 530642,
                                                                                                                                                                       'sha256': '32861aa7155d2e3f2e7a85bfed7d340759d2a0730784ef67134c24e21af8b363'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/OriginalSharpPrimeSynthesisProbe.lean': {'bytes': 14464,
                                                                                                                                                                                       'sha256': '40b0bc9e5680cf83cd0769b299f19c1d7fcc2332ef11f5504a6b5617290ebd1e'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/serialized-whole-synthesis-probe.log': {'bytes': 3579,
                                                                                                                                                                                      'sha256': 'c722c9da32531e45ad53be48753c8dad2bb52434c392588bf2b90bd23b2bf398'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/ACTUAL_SYNTHESIS_PROBE_RESULT.json': {'bytes': 5727,
                                                                                                                                                                                    'sha256': '1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'},
                '/workspace/p1-complete-proof/20261126-p15-synthesis-api-repair-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 539949,
                                                                                                                                                                            'sha256': '1f0815dbb5409e66f4b890eed13a3ad3ebd919130c5544aee37adf3da3d50bbd'},
                '/workspace/p1-complete-proof/20261126-p15-lowertrim-api-repair-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 549208,
                                                                                                                                                                            'sha256': '73cf0272db2e0e33c40462de795e6dc97c0c7b6ae4703b96fb0c94e1d4f31b03'},
                '/workspace/blue-member-build/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.lean': {'bytes': 8183,
                                                                                                         'sha256': '8b8987b5208aa0ed201adeb84a03076119519ff2880fb442175de2385b3ad049'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/normal/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/attempt-00000/normal-command.json': {'bytes': 1318,
                                                                                                                                                                                                                                                                             'sha256': 'a450854359288c2c10eb99178c44fc12b57ed86bfb13597f1cc99ccb6d2876a6'},
                '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/normal/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/attempt-00000/normal.log': {'bytes': 196840,
                                                                                                                                                                                                                                                                    'sha256': 'ba220ef31dbefca82c4bd3e1297980cb99d70d22024daf93d30ab09cdb7b7a92'},
                '/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.setup.json': {'bytes': 6425657,
                                                                                                                              'sha256': '9f9cf6315445e223e6a920e5e686e21a86d9a4a4ee26729f7740bf8fafcee3e3'}},
 'failed_artifact_observations': {'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': {'.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.c': None,
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.c.hash': None,
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.setup.json': {'bytes': 6425657,
                                                                                                                                                                          'sha256': '9f9cf6315445e223e6a920e5e686e21a86d9a4a4ee26729f7740bf8fafcee3e3'},
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.bc': None,
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.bc.hash': None,
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.o': None,
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.o.hash': None,
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.o.export': None,
                                                                                         '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.o.export.hash': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.olean': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.olean.hash': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.olean.private': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.olean.private.hash': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.olean.server': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.olean.server.hash': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.ilean': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.ilean.hash': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.trace': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.ir': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.ir.hash': None,
                                                                                         '.lake/build/lib/lean/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.ir.sig': None}},
 'current_read_live_source_count': 153,
 'current_read_preserved_dependency_count': 151}
CLAIMS = dict(normal_or_kernel_commands_executed=0, stock_readiness_executed_by_collector=False,
    types_or_archives_exported=False, axiom_union_exported=False, new_lean_acceptance=False,
    whole_P1_5_complete=False)
stage = 'require_frozen_actual_AE_evidence'


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
        need(record['source_commit'] == AE and record['published_source_count'] == 360 and
             all(record[k] == scope[k] for k in ('targets', 'accepted_owners', 'failures',
                 'reused_complete_selected_owners', 'selected_live_source_count')) and
             set(record['acceptance_bindings']) == set(accepted) and
             set(record['direct_import_readiness']) == set(scope['direct_import_readiness']) and
             all(record[k] is False for k in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not {'context_error', 'final_context_error', 'git_error'} & record.keys(), 'original AE scope differs')
    need(all(result.get(k) == v for k, v in worker.items()) and
         result['worker_exit_code'] == (0 if complete else 1) and
         result['all_selected_owners_accepted'] is complete, 'original AE terminal status differs')
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
                     runs[origins[module]][0]['acceptance_bindings'][module], 'same-AE reuse differs from first acceptance')
            else:
                need(module not in reused, 'reused owner lacks its original accepting run')
                origins[module] = index
    need(runs[0][0]['targets'] == [LOWERTRIM], 'LowerTrim first-run target identity differs')
    return origins


def read_run(driver, s, graph, index, fixed):
    run = ROOT / AE / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py'] + [
        stem+'_'+side+'.json' for stem in ('CONTEXT', 'GIT') for side in ('BEFORE', 'AFTER')]
    files = {name: bind(run/name) for name in names}
    need(set(fixed['pins']) == set(names)-{'executed-driver.py'} and
         all(pin(files[name]) == wanted for name, wanted in fixed['pins'].items()) and
         pin(files['executed-driver.py']) == DRIVER_FP, 'original AE run pins differ')
    result, worker, context = [s.api.read_json(run/name) for name in
        ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
    complete = validate_scope(result, worker, fixed['scope'])
    for stem in ('CONTEXT', 'GIT'):
        need(pin(files[stem+'_BEFORE.json']) == pin(files[stem+'_AFTER.json']), 'original context/Git pair changed')
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == AE and context['committed_inputs']['source_anchor_commit'] == AD and
         driver.selection(requested) == requested and set(requested) == set(result['targets']) and
         s.d.compile_order([], requested, graph) == result['targets'], 'requested/executed AE scope differs')
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
    driver.require_completed_existing_owner(s, AE, spec, module, spec.initial_owners[module])
    binding = driver.acceptance_binding(s, AE, module)
    need(binding == runs[index][0]['acceptance_bindings'][module], 'live owner binding differs from original accepting run')
    folder = ROOT/AE/module
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
    return {'source_commit': AE, 'source_sha256': spec.sources[module], 'source': bind(source),
        'compiler_job': runs[index][2]['compiler_job'], 'original_accepting_run': runs[index][2]['original_run'],
        'audit_id': fixed['audit_id'], 'owned_count': counts[0], 'public_count': counts[1],
        'owner_live_source_closure_count': own_closure,
        'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
        'receipt_paths': {key: value['path'] for key, value in receipts.items()},
        'normal_kernel_full_owned_revalidated_without_execution': True,
        'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
        'receipt_rebound_to_current_commit': False, 'later_same_AE_reuse_run': later_reuse[0] if later_reuse else None}


def identity(spec, selected):
    return dict(source_commit=AE, source_anchor_commit=AD, driver={'commit': AE, 'path': DRIVER, **DRIVER_FP},
        source_manifest={'commit': AE, 'path': MANIFEST, **MANIFEST_FP}, published_source_count=len(spec.graph),
        selected_owners_revalidated=selected, current_read_live_source_count=len(spec.active),
        current_read_preserved_dependency_count=len(spec.dependency_pins))


def flat_summary(runs, index, module, owner, common):
    run = runs[index][2]; files = run['evidence_bindings']
    groups = {k: run[k] for k in ('accepted_owners', 'reused_complete_selected_owners', 'failed_modules',
        'not_accepted_modules', 'not_started_modules', 'worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    return {**common, **CLAIMS, 'schema': 'p15_AE_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_AE_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'compiler_job': run['compiler_job'],
        'original_run': 'runs/attempt-%05d' % index, 'original_result': pin(files['RESULT.json']),
        'original_worker_result': pin(files['WORKER_RESULT.json']), 'original_requested_targets': run['original_requested_targets'],
        'original_targets': run['targets'], **{'original_group_'+k: v for k, v in groups.items()},
        'original_group_live_closure_count': run['original_live_source_count'],
        'original_context_pairs': {stem: {side: pin(files[stem+'_'+side.upper()+'.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'], 'owners': {module: owner},
        'owner_live_source_closure_count': owner['owner_live_source_closure_count'],
        'later_same_source_reuse': runs[1][2] if owner['later_same_AE_reuse_run'] else None,
        'source_runtime_and_original_receipts_unchanged': True}


def collect():
    global stage
    need(__debug__, 'optimized Python refused')
    need(isinstance(PINNED, dict) and PINNED.get('schema') == 'p15_AE_fixed_actual_collection_inputs_v1',
         'actual AE later4 outcome and raw run/owner pins are not yet frozen')
    need(len(PINNED['runs']) == 2 and isinstance(PINNED['owners'], dict) and PINNED['owners'] and
         all(re.fullmatch('job_[0-9a-f]{32}', r['compiler_job']) for r in PINNED['runs']),
         'fixed actual runs/accepted-owner pins incomplete; no acceptance collection attempted')
    need(PINNED['runs'][0]['scope']['targets'] == [LOWERTRIM] and
         PINNED['runs'][0]['scope']['selected_live_source_count'] == 119 and
         PINNED['runs'][1]['scope']['selected_live_source_count'] == 157 and
         len(PINNED['runs'][1]['scope']['targets']) == 4 and
         PINNED['runs'][1]['scope']['targets'][0] == LOWERTRIM,
         'fixed AE first119/later4 source scope differs')
    # First process-environment access: unbound PINNED has already held.
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    stage = 'load_published_AE_reader'
    raw, manifest_raw = [subprocess.check_output(['git', 'show', AE+':'+path], cwd=REPO) for path in (DRIVER, MANIFEST)]
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published AE reader/manifest differs')
    executed = ROOT/AE/'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'original AE executed reader differs')
    driver = ModuleType('unchanged_AE_acceptance_reader'); driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, AD), 'AE reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    trees = {c: tree_inventory(ROOT/c) for c in (AE, AC, AA, Y, W, U, S, Q)}
    extras = {p: file_fp(p) for p in PINNED['extra_pins']}
    need(extras == PINNED['extra_pins'], 'fixed extra evidence differs')
    for module, expected in PINNED['failed_artifact_observations'].items():
        need(set(expected) == set(driver.artifact_paths(module)) and driver.module_artifacts(s, module) == expected,
             'original failed owner artifact slots differ: '+module)
    manifest = json.loads(manifest_raw); graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    stage = 'read_two_original_AE_runs'
    runs = [read_run(driver, s, graph, i, fixed) for i, fixed in enumerate(PINNED['runs'])]
    need(runs[0][0]['targets'] == [LOWERTRIM] and
         runs[1][0]['targets'] == manifest['selection_guidance']['subsequent_4_targets'] and
         len(manifest['previously_accepted_targets']) == 14 and
         manifest['previously_accepted_targets'] == driver.PREVIOUSLY_ACCEPTED_TARGETS,
         'first/later target scopes or fourteen inherited prior identities differ')
    origins = accepting_runs(runs); selected = list(origins)
    need(set(origins) == set(PINNED['owners']) and all(PINNED['owners'][m]['accepting_run_index'] == i for m, i in origins.items()),
         'frozen owner accepting-run mapping differs')
    names = [PINNED['owners'][m]['public_name'] for m in selected]
    need(len(names) == len(set(names)) and all(re.fullmatch('[A-Za-z0-9_]+_AE_PUBLIC_ACCEPTANCE', n) for n in names),
         'owner public-summary names collide or differ')
    stage = 'original_AE_preflight_for_actual_accepted_prefix'
    spec = driver.preflight(s, AE, selected)
    need(len(spec.graph) == 360 and len(spec.active) == PINNED['current_read_live_source_count'] and
         len(spec.dependency_pins) == PINNED['current_read_preserved_dependency_count'] and
         spec.order == selected and set(spec.initial_owners) == set(selected), 'actual accepted-prefix read scope differs')
    for result, context, _ in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active-set(result['targets']), 'original AE context inventory differs')
    remaining_failed = {m for result, _, _ in runs for m in result['failures']} - set(origins)
    need(set(PINNED['failed_artifact_observations']) == remaining_failed,
         'remaining failed-owner artifact inventory is incomplete or stale')
    failure_observations = {}
    for module in sorted(remaining_failed):
        source = PROJECT/s.h.module_path(module)
        need(str(source) in extras and extras[str(source)] ==
             {k: manifest['project_sources'][module][k] for k in ('bytes', 'sha256')},
             'failed owner source is not pinned to the original AE source: '+module)
        normal_prefix = module+'/normal/'
        failure_observations[module] = {
            'source': bind(source), 'artifact_slots': PINNED['failed_artifact_observations'][module],
            'normal_evidence': {str(ROOT/AE/path): observed for path, observed in trees[AE].items()
                                if path.startswith(normal_prefix) and observed != 'directory'},
            'normal_receipt': str(ROOT/AE/module/'normal'/module/'NORMAL_PASS.json'),
            'normal_receipt_observation': trees[AE].get(module+'/normal/'+module+'/NORMAL_PASS.json'),
            'acceptance_claimed': False}
    artifacts = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    def target_sources():
        return {m: file_fp(PROJECT/s.h.module_path(m)) if os.path.lexists(PROJECT/s.h.module_path(m)) else None for m in driver.TARGETS}
    sources_before = target_sources()
    owners = {}
    for module, index in origins.items():
        stage = 'revalidate_original_AE_owner:'+module
        owners[module] = read_owner(driver, s, spec, runs, module, index, PINNED['owners'][module])
    stage = 'verify_read_only_preservation'
    need(driver.snapshot(s, spec) == spec.baseline and target_sources() == sources_before and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts and
         {p: file_fp(p) for p in extras} == extras and {c: tree_inventory(ROOT/c) for c in trees} == trees and
         s.d.original_git_state(REPO) == git_before, 'source/runtime/artifacts/original-evidence/Git changed during collection')
    common = identity(spec, selected)
    return {**common, **CLAIMS, 'schema': 'p15_AE_original_accepted_prefix_read_v1',
        'status': 'ORIGINAL_AE_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'collector': {'filename': Path(__file__).name, **file_fp(__file__)},
        'frozen_actual_input_binding': value_fp(PINNED),
        'public_summaries': {PINNED['owners'][m]['public_name']: flat_summary(runs, origins[m], m, row, common) for m, row in owners.items()},
        'original_runs': [r[2] for r in runs],
        'historical_owners_revalidated_in_current_read_scope': {m: {k: row[k] for k in
            ('source_commit', 'source_sha256', 'owned_count', 'public_count')} for m, row in spec.supplier_evidence.items()},
        'complete_original_AE_AC_AA_Y_W_U_S_Q_evidence_inventory': {c: {'entry_count': len(t), **value_fp(t)} for c, t in trees.items()},
        'preserved_extra_evidence': extras, 'current_read_snapshot': value_fp(spec.baseline),
        'inherited_previous_target_count': 14,
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
