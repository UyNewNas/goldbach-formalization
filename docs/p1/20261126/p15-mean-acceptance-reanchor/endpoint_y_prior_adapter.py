

# Fixed Endpoint@Y acceptance; original Y later7 remains partial.
ENDPOINT_Y_MODULE = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
ENDPOINT_Y_FAILED_MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
ENDPOINT_Y_PRIOR_SOURCE_ANCHOR = '09bf8a02b4c96798930abe2826cfb27529c01ad3'
ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS = {'ImbalancedChen.P5OriginalPrimeEndpointLogPayment': {'group': 'endpoint_y',
                                                      'source_commit': 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
                                                      'source_sha256': '1a9baa44f798fba58671d473f3be4def2eaefd6c758413e0f7d60b3238edef3c',
                                                      'live_source_closure_count': 110,
                                                      'historical_group': {'source_commit': 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
                                                                           'compiler_job': 'job_8f89803dbab64592982477c8613b24c1',
                                                                           'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                                                                           'run': 'runs/attempt-00000',
                                                                           'owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                                                                           'driver': {'bytes': 223361,
                                                                                      'commit': 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
                                                                                      'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
                                                                                      'sha256': 'e84c943388675d65c63b701c1663f030ec3c340e22d1ee31fa1c1ada3bc67918'},
                                                                           'source_graph': {'bytes': 357110,
                                                                                            'commit': 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
                                                                                            'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
                                                                                            'sha256': '25eef56e95dee4c5ef7308b49b35bf125dc79af032fd5bef0e658bed8001a04a'},
                                                                           'published_source_count': 360,
                                                                           'public_evidence': {'commit': 'bde4a91307cb5e5872b6fc3c1e4a1520908b10c2',
                                                                                               'path': 'docs/p1/20261125/p15-current-public-acceptance/ENDPOINT_Y_PUBLIC_ACCEPTANCE.json',
                                                                                               'bytes': 12271,
                                                                                               'sha256': '4ca613c9dac4ff86f21b0728977f0f9c66ad1f0acd2abf99a8da87a7de8d461b'},
                                                                           'evidence_kind': 'bounded_public_acceptance'},
                                                      'owned_count': 24,
                                                      'public_count': 24,
                                                      'audit_id': 'a602bb782d20fdd11079'}}
ENDPOINT_Y_PRIOR_RUNS = {'ImbalancedChen.P5OriginalPrimeEndpointLogPayment': {'targets': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                                                      'accepted': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                                                      'reused': [],
                                                      'failed': [],
                                                      'not_accepted': [],
                                                      'not_started': [],
                                                      'readiness': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
                                                      'exit_code': 0,
                                                      'live_count': 110,
                                                      'result': {'bytes': 8702,
                                                                 'sha256': 'ee4f055634e6e56673e586fe3db1998ff10d7a45c8f99907481461292b8edb58'},
                                                      'worker': {'bytes': 8637,
                                                                 'sha256': '744a42fc02e4fb9d9134b7a15bf38b552b0e6d51e7dbc2732baa7a85f5af3965'},
                                                      'requested_targets': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment']}}
ENDPOINT_Y_LATER_PINS = {'CONTEXT_AFTER.json': {'bytes': 506374,
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
                        'sha256': '4a12b1cacaaa5fa6db440b79b34e9ac4b7e5c0208f2dd3dd9ac5e8340e65575b'},
 'executed-driver.py': {'bytes': 223361,
                        'sha256': 'e84c943388675d65c63b701c1663f030ec3c340e22d1ee31fa1c1ada3bc67918'}}
ENDPOINT_Y_LATER_TARGETS = ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
 'ImbalancedChen.P5PrimeDivisorMeanCorrection',
 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
ENDPOINT_Y_LATER_RECORD = {'accepted_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
 'all_selected_owners_accepted': False,
 'compiler_job': 'job_579a949c0cfa4b85a4b678592bbc7295',
 'dispatch_error': 'serialized worker exited 1',
 'evidence_bindings': {'CONTEXT_AFTER.json': {'bytes': 506374,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001/CONTEXT_AFTER.json',
                                              'sha256': 'cd603957864771e99195597935aebc1e822970c36ce4c02d88a4d621ef2ba22d'},
                       'CONTEXT_BEFORE.json': {'bytes': 506374,
                                               'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001/CONTEXT_BEFORE.json',
                                               'sha256': 'cd603957864771e99195597935aebc1e822970c36ce4c02d88a4d621ef2ba22d'},
                       'GIT_AFTER.json': {'bytes': 1157,
                                          'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001/GIT_AFTER.json',
                                          'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                       'GIT_BEFORE.json': {'bytes': 1157,
                                           'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001/GIT_BEFORE.json',
                                           'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                       'RESULT.json': {'bytes': 50678,
                                       'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001/RESULT.json',
                                       'sha256': '11fe73336284239346394cd6c1480cc9cfc94a883dddfcacd71230ab3492a53d'},
                       'WORKER_RESULT.json': {'bytes': 50562,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001/WORKER_RESULT.json',
                                              'sha256': '4a12b1cacaaa5fa6db440b79b34e9ac4b7e5c0208f2dd3dd9ac5e8340e65575b'},
                       'executed-driver.py': {'bytes': 223361,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001/executed-driver.py',
                                              'sha256': 'e84c943388675d65c63b701c1663f030ec3c340e22d1ee31fa1c1ada3bc67918'}},
 'failed_modules': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
 'failure_messages': {'ImbalancedChen.P5PrimeDivisorMeanCorrection': 'normal failed/scope differs: '
                                                                     'ImbalancedChen.P5PrimeDivisorMeanCorrection'},
 'not_accepted_modules': ['ImbalancedChen.P5PrimeDivisorMeanCorrection',
                          'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                          'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                          'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                          'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                          'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
 'not_started_modules': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                         'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                         'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                         'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                         'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
 'original_context_pairs_equal': True,
 'original_final_stock_readiness': {'executed_again_by_collector': False,
                                    'reason': 'original_attempt_stopped_after_owner_failure',
                                    'recorded': False},
 'original_live_source_count': 157,
 'original_requested_targets': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                                'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                                'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                                'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime',
                                'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
                                'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                                'ImbalancedChen.P5PrimeDivisorMeanCorrection'],
 'original_run': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00001',
 'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
 'source_commit': 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
 'status': 'PARTIAL_FAILURE_AFTER_ACCEPTED_PREFIX',
 'targets': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
             'ImbalancedChen.P5PrimeDivisorMeanCorrection',
             'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
             'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
             'ImbalancedChen.P1OriginalSingletonAtlasTrim',
             'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
             'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
 'worker_exit_code': 1}
PREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS}


def endpoint_y_prior_source_binding(s, graph, sources, module, prior):
    require(module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS and prior == ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS[module] and
            sources[module] == prior['source_sha256'] and
            len(s.h.closure(graph, [module])) == prior['live_source_closure_count'],
            'fixed Endpoint@Y prior source/own closure differs: ' + module)


def require_endpoint_y_prior_scope(module, prior, public, original, worker):
    require(module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS and prior == ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS[module],
            'unknown or changed fixed Endpoint@Y prior')
    fixed, run_scope = prior['historical_group'], ENDPOINT_Y_PRIOR_RUNS[module]
    expected = {
        'schema': 'p15_Y_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_Y_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': prior['source_commit'], 'source_anchor_commit': ENDPOINT_Y_PRIOR_SOURCE_ANCHOR,
        'compiler_job': fixed['compiler_job'], 'driver': fixed['driver'],
        'source_manifest': fixed['source_graph'], 'original_run': fixed['run'],
        'original_result': run_scope['result'], 'original_worker_result': run_scope['worker'],
        'original_requested_targets': run_scope['requested_targets'], 'original_targets': run_scope['targets'],
        'original_group_accepted_owners': run_scope['accepted'],
        'original_group_reused_complete_selected_owners': run_scope['reused'],
        'original_group_failed_modules': run_scope['failed'],
        'original_group_not_accepted_modules': run_scope['not_accepted'],
        'original_group_not_started_modules': run_scope['not_started'],
        'original_group_worker_exit_code': run_scope['exit_code'],
        'original_group_all_selected_owners_accepted': run_scope['exit_code'] == 0,
        'original_group_dispatch_error': None if run_scope['exit_code'] == 0 else 'serialized worker exited 1',
        'original_group_live_closure_count': run_scope['live_count'], 'published_source_count': 360,
        'selected_owners_revalidated': list(ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS),
        'current_read_live_source_count': 110, 'current_read_preserved_dependency_count': 109,
        'owner_live_source_closure_count': prior['live_source_closure_count'],
        'source_runtime_and_original_receipts_unchanged': True, 'normal_or_kernel_commands_executed': 0,
        'types_or_archives_exported': False, 'axiom_union_exported': False,
        'new_lean_acceptance': False, 'whole_P1_5_complete': False,
        'stock_readiness_executed_by_collector': False,
        'later_same_source_reuse': ENDPOINT_Y_LATER_RECORD,
    }
    require(all(public.get(key) == value and type(public.get(key)) is type(value)
                for key, value in expected.items()) and set(public['owners']) == {module},
            'fixed Endpoint@Y public identity/run/actual joint collection scope differs: ' + module)
    owner = public['owners'][module]
    base = Path(fixed['evidence_root']) / prior['source_commit']
    run, folder = base / fixed['run'], base / module
    audit = folder / 'audits' / prior['audit_id']
    paths = {'normal': str(folder / 'normal' / module / 'NORMAL_PASS.json'),
             'audit_plan': str(audit / 'AUDIT_PLAN.json'),
             'audit_result': str(audit / 'lane-0/VALIDATION_RESULTS.json'),
             'owned_exports': str(audit / 'lane-0/OWNED_EXPORTS.json'),
             'owned_log': str(audit / 'lane-0/all-owned-types-axioms.log'),
             'reused_normal_evidence': str(audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json')}
    receipts = owner['receipt_bindings']
    require(owner['source_commit'] == prior['source_commit'] and owner['source_sha256'] == prior['source_sha256'] and
            owner['compiler_job'] == fixed['compiler_job'] and owner['original_accepting_run'] == str(run) and
            owner['owner_live_source_closure_count'] == prior['live_source_closure_count'] and
            type(owner['owned_count']) is int and type(owner['public_count']) is int and
            (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
                (prior['owned_count'], prior['public_count'], prior['audit_id']) and
            owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
            owner['source_plus_five_and_all_21_artifacts_bound_to_original_result'] is True and
            owner['receipt_rebound_to_current_commit'] is False and owner['receipt_paths'] == paths and
            owner['later_same_Y_reuse_run'] == (str(base / 'runs/attempt-00001') if module == ENDPOINT_Y_MODULE else None) and
            set(receipts) == set(paths) and all(valid_fingerprint(receipts[key]) for key in paths) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and valid_fingerprint(pair['before']) and
                pair['before'] == pair['after'] for pair in public['original_context_pairs'].values()),
            'fixed Endpoint@Y owner/count/six-receipt/context identity differs: ' + module)
    for record in (original, worker):
        require(record['source_commit'] == prior['source_commit'] and record['targets'] == run_scope['targets'] and
                record['accepted_owners'] == run_scope['accepted'] and set(record['failures']) == set(run_scope['failed']) and
                set(record['acceptance_bindings']) == set(run_scope['accepted']) and
                record['reused_complete_selected_owners'] == run_scope['reused'] and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == run_scope['live_count'] and
                set(record['direct_import_readiness']) == set(run_scope['readiness']) and
                record['whole_P1_complete'] is False and record['whole_P1_5_complete'] is False and
                all(record[key] is False for key in ('accepted_supplier_recompile_requested',
                    'dependency_rebuild_requested', 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error')),
                'fixed original Y RESULT/WORKER scope differs: ' + module)
    require(original['worker_exit_code'] == run_scope['exit_code'] and
            original['all_selected_owners_accepted'] is (run_scope['exit_code'] == 0) and
            'dispatch_error' not in worker and
            all(original[key] == worker[key] for key in ('targets', 'accepted_owners', 'failures',
                'acceptance_bindings', 'direct_import_readiness', 'original_supplier_acceptance_bindings')),
            'original Y RESULT/WORKER identity differs: ' + module)
    ready = original['direct_import_readiness'][module]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == [],
            'accepted Endpoint@Y owner direct-import readiness differs: ' + module)
    stock = public['original_final_stock_readiness']
    if run_scope['exit_code'] == 0:
        require('dispatch_error' not in original and original['final_stock_readiness'] == worker['final_stock_readiness'] and
                all(record['exit_code'] == 0 and record['actual_built_modules'] == [] and record['actual_failed_modules'] == []
                    for record in (stock, original['final_stock_readiness'])) and
                stock['recorded'] is True and stock['executed_again_by_collector'] is False and
                all(stock[key]['path'] == str(run / name) and valid_fingerprint({k: stock[key][k] for k in ('bytes', 'sha256')})
                    for key, name in (('command', 'final-stock-readiness-command.json'), ('log', 'final-stock-readiness.log'))),
                'original Endpoint successful final stock readiness differs')
    else:
        require(original['dispatch_error'] == 'serialized worker exited 1' and
                'final_stock_readiness' not in original and 'final_stock_readiness' not in worker and
                stock == {'recorded': False, 'reason': 'original_attempt_stopped_after_owner_failure',
                          'executed_again_by_collector': False},
                'original later13 partial failure/final stock absence differs')
    binding = original['acceptance_bindings'][module]
    require(binding['module'] == module and binding['normal_receipt'] == {'path': paths['normal'], **receipts['normal']} and
            binding['audits'] == [{'plan': {'path': paths['audit_plan'], **receipts['audit_plan']},
                                  'result': {'path': paths['audit_result'], **receipts['audit_result']}}],
            'Endpoint@Y public receipt paths/pins differ from original acceptance: ' + module)


def retained_endpoint_y_prior_target(s, spec, module):
    require(module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS and module in spec.active and module not in spec.selected,
            'Endpoint@Y prior reuse is outside the actual dependency scope: ' + module)
    prior = spec.manifest['previously_accepted_targets'][module]
    endpoint_y_prior_source_binding(s, spec.graph, spec.sources, module, prior)
    require(module not in spec.manifest['accepted_suppliers'] and prior['group'] not in spec.manifest['accepted_supplier_groups'],
            'Endpoint@Y prior overlay group collides: ' + module)
    fixed, run_scope = prior['historical_group'], ENDPOINT_Y_PRIOR_RUNS[module]
    public = json.loads(published_binding(fixed['public_evidence']))
    base = Path(fixed['evidence_root']) / prior['source_commit']
    run = base / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', run_scope['result']))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', run_scope['worker']))
    require_endpoint_y_prior_scope(module, prior, public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'original Y context/Git pair differs: ' + module)
    if run_scope['exit_code'] == 0:
        stock = original['final_stock_readiness']
        public_stock = public['original_final_stock_readiness']
        command = json.loads(retained_read(s, spec, run / 'final-stock-readiness-command.json',
                                         {k: public_stock['command'][k] for k in ('bytes', 'sha256')}))
        require(command == stock and stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + module + ':olean']) and
                stock['cwd'] == str(PROJECT) and stock['log'] == str(run / 'final-stock-readiness.log') and
                {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']} ==
                    {k: public_stock['log'][k] for k in ('bytes', 'sha256')},
                'original Endpoint guarded final stock command/log binding differs')
        retained_read(s, spec, Path(stock['log']), {k: public_stock['log'][k] for k in ('bytes', 'sha256')})
    later_run = base / 'runs/attempt-00001'
    require(retained_read(s, spec, later_run / 'executed-driver.py',
            ENDPOINT_Y_LATER_PINS['executed-driver.py']) == published_binding(fixed['driver']),
            'original Y later executed driver differs')
    later = json.loads(retained_read(s, spec, later_run / 'RESULT.json', ENDPOINT_Y_LATER_PINS['RESULT.json']))
    later_worker = json.loads(retained_read(s, spec, later_run / 'WORKER_RESULT.json', ENDPOINT_Y_LATER_PINS['WORKER_RESULT.json']))
    for record in (later, later_worker):
        require(record['source_commit'] == prior['source_commit'] and
                record['targets'] == ENDPOINT_Y_LATER_TARGETS and record['accepted_owners'] == [module] and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == 157 and
                set(record['direct_import_readiness']) == {ENDPOINT_Y_FAILED_MEAN} and
                all(record[key] is False for key in ('whole_P1_complete', 'accepted_supplier_recompile_requested',
                    'dependency_rebuild_requested', 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error')) and
                record['reused_complete_selected_owners'] == [module] and
                record['failures'] == {ENDPOINT_Y_FAILED_MEAN: 'normal failed/scope differs: ' + ENDPOINT_Y_FAILED_MEAN} and
                set(record['acceptance_bindings']) == {module} and
                record['acceptance_bindings'][module] == original['acceptance_bindings'][module] and
                'final_stock_readiness' not in record and record['whole_P1_5_complete'] is False,
                'original Y later7 failure or Endpoint reuse identity differs')
    require(later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            later['dispatch_error'] == 'serialized worker exited 1' and
            all(later.get(key) == value for key, value in later_worker.items()),
            'original Y later7 RESULT/WORKER terminal status differs')
    for stem in ('CONTEXT', 'GIT'):
        require(retained_read(s, spec, later_run / (stem + '_BEFORE.json'), ENDPOINT_Y_LATER_PINS[stem + '_BEFORE.json']) ==
                retained_read(s, spec, later_run / (stem + '_AFTER.json'), ENDPOINT_Y_LATER_PINS[stem + '_AFTER.json']),
                'original Y later7 context/Git pair differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Endpoint@Y prior live source/full21 artifacts differ from original acceptance: ' + module)
    shadow = SimpleNamespace(**spec.__dict__)
    shadow.manifest = {**spec.manifest,
        'accepted_suppliers': {**spec.manifest['accepted_suppliers'], module: {
            'group': prior['group'], 'source_commit': prior['source_commit'], 'source_sha256': prior['source_sha256']}},
        'accepted_supplier_groups': {**spec.manifest['accepted_supplier_groups'], prior['group']: fixed}}
    owner = retained_owner(s, shadow, module, validate_live=True)
    evidence = spec.supplier_evidence[module]
    require(evidence['source_commit'] == prior['source_commit'] and
            evidence['selected_supplier_live_closure_count'] == prior['live_source_closure_count'] and
            evidence['original_group_worker_exit_code'] == run_scope['exit_code'] and
            evidence['owned_count'] == prior['owned_count'] and evidence['public_count'] == prior['public_count'] and
            Path(evidence['audit_plan']['path']).parent.name == prior['audit_id'] and
            module_artifacts(s, module) == expected and s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Endpoint@Y prior full audit/count/source/full21 post-validation differs: ' + module)
    spec.dependency_pins[module] = expected
    return owner


