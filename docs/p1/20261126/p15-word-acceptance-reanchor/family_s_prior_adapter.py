

# Fixed Family@S acceptance; original successful and later partial runs stay S.
FAMILY_S_MODULE = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
FAMILY_S_FAILED_WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
FAMILY_S_PRIOR_SOURCE_ANCHOR = '0935516b9bd978a61248c81b59776d1eb47f6044'
FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS = {'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound': {'group': 'family_s',
                                                         'source_commit': '18e41c4a1c01ca22e5537acb934e04891279b616',
                                                         'source_sha256': '4f58683304250030edbca5d1ed4f27eaa06c6de18fb0bbdcad4b2101df0ab109',
                                                         'live_source_closure_count': 75,
                                                         'historical_group': {'source_commit': '18e41c4a1c01ca22e5537acb934e04891279b616',
                                                                              'compiler_job': 'job_bf1ad9f0adbc4c8a9fe4b05e99addf4d',
                                                                              'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                                                                              'run': 'runs/attempt-00000',
                                                                              'owners': ['ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'],
                                                                              'driver': {'commit': '18e41c4a1c01ca22e5537acb934e04891279b616',
                                                                                         'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
                                                                                         'bytes': 130643,
                                                                                         'sha256': 'fdd3218c5e5d3169bd42ca8ba1953c8378f9b2c436107ed165a13068a48d2c55'},
                                                                              'source_graph': {'commit': '18e41c4a1c01ca22e5537acb934e04891279b616',
                                                                                               'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
                                                                                               'bytes': 346806,
                                                                                               'sha256': '1c6d8499822f69f35469c4bbc222f85d1e46d6a5c977bd4f5c4cdd649520ba86'},
                                                                              'published_source_count': 360,
                                                                              'public_evidence': {'commit': '999510c460e6e026c8cabe46c5f35876f7201f8e',
                                                                                                  'path': 'docs/p1/20261125/p15-current-public-acceptance/FAMILY_S_PUBLIC_ACCEPTANCE.json',
                                                                                                  'bytes': 13244,
                                                                                                  'sha256': '12f18cc8e6160e645c17a7b7f5ae94f616d7c940a97289080698aaaee973fcfa'},
                                                                              'evidence_kind': 'bounded_public_acceptance'},
                                                         'owned_count': 27,
                                                         'public_count': 27,
                                                         'audit_id': 'b2f9953a401fa5dd488b'}}
FAMILY_S_PRIOR_RUNS = {'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound': {'targets': ['ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'],
                                                         'accepted': ['ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'],
                                                         'reused': [],
                                                         'failed': [],
                                                         'not_accepted': [],
                                                         'not_started': [],
                                                         'readiness': ['ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'],
                                                         'exit_code': 0,
                                                         'live_count': 75,
                                                         'result': {'bytes': 37042,
                                                                    'sha256': '554af002bced1b2b2fcfa71834dfc3412684d9214106742d5d0a927dd57546f7'},
                                                         'worker': {'bytes': 36977,
                                                                    'sha256': 'a456196896172094854f8f6d22dfcd0afa32afd3329e503620c9e4a5623e6548'},
                                                         'requested_targets': ['ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound']}}
FAMILY_S_LATER_PINS = {'RESULT.json': {'bytes': 43984,
                 'sha256': '5e909125e1e23eeca59699eb4ff834e2abde2ce148a8530863283101e2586bfc'},
 'WORKER_RESULT.json': {'bytes': 43868,
                        'sha256': 'f3bc0dbb2fe93c8b1090b34da8ad81f37bcce1192dd137cafe2912c83e08fc4b'},
 'CONTEXT_BEFORE.json': {'bytes': 474301,
                         'sha256': '6e1db877be24eb5b46e21176be223573214267e461bffacdf9a9f2dd79f6607b'},
 'CONTEXT_AFTER.json': {'bytes': 474301,
                        'sha256': '6e1db877be24eb5b46e21176be223573214267e461bffacdf9a9f2dd79f6607b'},
 'GIT_BEFORE.json': {'bytes': 1157,
                     'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
 'GIT_AFTER.json': {'bytes': 1157,
                    'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}}
FAMILY_S_LATER_TARGETS = ['ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound',
 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
 'ImbalancedChen.P1OriginalSingletonSmoothLicence',
 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
 'ImbalancedChen.P5PrimeDivisorMeanCorrection',
 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
PREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS}


def family_s_prior_source_binding(s, graph, sources, module, prior):
    require(module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS and prior == FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS[module] and
            sources[module] == prior['source_sha256'] and
            len(s.h.closure(graph, [module])) == prior['live_source_closure_count'],
            'fixed Family@S prior source/own closure differs: ' + module)


def require_family_s_prior_scope(module, prior, public, original, worker):
    require(module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS and prior == FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS[module],
            'unknown or changed fixed Family@S prior')
    fixed, run_scope = prior['historical_group'], FAMILY_S_PRIOR_RUNS[module]
    expected = {
        'schema': 'p15_S_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_S_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': prior['source_commit'], 'source_anchor_commit': FAMILY_S_PRIOR_SOURCE_ANCHOR,
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
        'selected_owners_revalidated': list(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS),
        'current_read_live_source_count': 75, 'current_read_preserved_dependency_count': 74,
        'owner_live_source_closure_count': prior['live_source_closure_count'],
        'source_runtime_and_original_receipts_unchanged': True, 'normal_or_kernel_commands_executed': 0,
        'types_or_archives_exported': False, 'axiom_union_exported': False,
        'new_lean_acceptance': False, 'whole_P1_5_complete': False,
    }
    require(all(public.get(key) == value and type(public.get(key)) is type(value)
                for key, value in expected.items()) and set(public['owners']) == {module},
            'fixed Family@S public identity/run/actual joint collection scope differs: ' + module)
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
            owner['later_same_S_reuse_run'] == (str(base / 'runs/attempt-00001') if module == FAMILY_S_MODULE else None) and
            set(receipts) == set(paths) and all(valid_fingerprint(receipts[key]) for key in paths) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and valid_fingerprint(pair['before']) and
                pair['before'] == pair['after'] for pair in public['original_context_pairs'].values()),
            'fixed Family@S owner/count/six-receipt/context identity differs: ' + module)
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
                'fixed original S RESULT/WORKER scope differs: ' + module)
    require(original['worker_exit_code'] == run_scope['exit_code'] and
            original['all_selected_owners_accepted'] is (run_scope['exit_code'] == 0) and
            'dispatch_error' not in worker and
            all(original[key] == worker[key] for key in ('targets', 'accepted_owners', 'failures',
                'acceptance_bindings', 'direct_import_readiness', 'original_supplier_acceptance_bindings')),
            'original S RESULT/WORKER identity differs: ' + module)
    ready = original['direct_import_readiness'][module]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == [],
            'accepted Family@S owner direct-import readiness differs: ' + module)
    stock = public['original_final_stock_readiness']
    if run_scope['exit_code'] == 0:
        require('dispatch_error' not in original and original['final_stock_readiness'] == worker['final_stock_readiness'] and
                all(record['exit_code'] == 0 and record['actual_built_modules'] == [] and record['actual_failed_modules'] == []
                    for record in (stock, original['final_stock_readiness'])) and
                stock['recorded'] is True and stock['executed_again_by_collector'] is False and
                all(stock[key]['path'] == str(run / name) and valid_fingerprint({k: stock[key][k] for k in ('bytes', 'sha256')})
                    for key, name in (('command', 'final-stock-readiness-command.json'), ('log', 'final-stock-readiness.log'))),
                'original Family successful final stock readiness differs')
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
            'Family@S public receipt paths/pins differ from original acceptance: ' + module)


def retained_family_s_prior_target(s, spec, module):
    require(module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS and module in spec.active and module not in spec.selected,
            'Family@S prior reuse is outside the actual dependency scope: ' + module)
    prior = spec.manifest['previously_accepted_targets'][module]
    family_s_prior_source_binding(s, spec.graph, spec.sources, module, prior)
    require(module not in spec.manifest['accepted_suppliers'] and prior['group'] not in spec.manifest['accepted_supplier_groups'],
            'Family@S prior overlay group collides: ' + module)
    fixed, run_scope = prior['historical_group'], FAMILY_S_PRIOR_RUNS[module]
    public = json.loads(published_binding(fixed['public_evidence']))
    base = Path(fixed['evidence_root']) / prior['source_commit']
    run = base / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', run_scope['result']))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', run_scope['worker']))
    require_family_s_prior_scope(module, prior, public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'original S context/Git pair differs: ' + module)
    if run_scope['exit_code'] == 0:
        stock = original['final_stock_readiness']
        public_stock = public['original_final_stock_readiness']
        command = json.loads(retained_read(s, spec, run / 'final-stock-readiness-command.json',
                                         {k: public_stock['command'][k] for k in ('bytes', 'sha256')}))
        require(command == stock and stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + module + ':olean']) and
                stock['cwd'] == str(PROJECT) and stock['log'] == str(run / 'final-stock-readiness.log') and
                {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']} ==
                    {k: public_stock['log'][k] for k in ('bytes', 'sha256')},
                'original Family guarded final stock command/log binding differs')
        retained_read(s, spec, Path(stock['log']), {k: public_stock['log'][k] for k in ('bytes', 'sha256')})
    later_run = base / 'runs/attempt-00001'
    later = json.loads(retained_read(s, spec, later_run / 'RESULT.json', FAMILY_S_LATER_PINS['RESULT.json']))
    later_worker = json.loads(retained_read(s, spec, later_run / 'WORKER_RESULT.json', FAMILY_S_LATER_PINS['WORKER_RESULT.json']))
    for record in (later, later_worker):
        require(record['source_commit'] == prior['source_commit'] and
                record['targets'] == FAMILY_S_LATER_TARGETS and record['accepted_owners'] == [module] and
                record['reused_complete_selected_owners'] == [module] and
                record['failures'] == {FAMILY_S_FAILED_WORD: 'normal failed/scope differs: ' + FAMILY_S_FAILED_WORD} and
                set(record['acceptance_bindings']) == {module} and
                record['acceptance_bindings'][module] == original['acceptance_bindings'][module] and
                'final_stock_readiness' not in record and record['whole_P1_5_complete'] is False,
                'original S later11 failure or Family reuse identity differs')
    require(later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            later['dispatch_error'] == 'serialized worker exited 1' and
            all(later.get(key) == value for key, value in later_worker.items()),
            'original S later11 RESULT/WORKER terminal status differs')
    for stem in ('CONTEXT', 'GIT'):
        require(retained_read(s, spec, later_run / (stem + '_BEFORE.json'), FAMILY_S_LATER_PINS[stem + '_BEFORE.json']) ==
                retained_read(s, spec, later_run / (stem + '_AFTER.json'), FAMILY_S_LATER_PINS[stem + '_AFTER.json']),
                'original S later11 context/Git pair differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Family@S prior live source/full21 artifacts differ from original acceptance: ' + module)
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
            'Family@S prior full audit/count/source/full21 post-validation differs: ' + module)
    spec.dependency_pins[module] = expected
    return owner


