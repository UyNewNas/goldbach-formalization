

# Fixed Synthesis@AC acceptance; original AC later5 remains partial.
SYNTHESIS_AC_MODULE = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
SYNTHESIS_AC_FAILED_LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
SYNTHESIS_AC_PRIOR_SOURCE_ANCHOR = '60e6b6e18fbda5f6b0e997d15392b32100e854d9'
SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS = {'ImbalancedChen.P5OriginalSharpPrimeSynthesis': {'group': 'synthesis_ac',
                                                  'source_commit': '9f2013ad9cb9caac9cec03cb213d9949c4443c65',
                                                  'source_sha256': '990ceec9aae74a67c7e1b25e94d66b33644214e1fc0bb3193275ed1b09c50322',
                                                  'live_source_closure_count': 112,
                                                  'historical_group': {'source_commit': '9f2013ad9cb9caac9cec03cb213d9949c4443c65',
                                                                       'compiler_job': 'job_b4464fff4b944230927c0f40b7cd1632',
                                                                       'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                                                                       'run': 'runs/attempt-00000',
                                                                       'owners': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                                                                       'driver': {'bytes': 278990,
                                                                                  'commit': '9f2013ad9cb9caac9cec03cb213d9949c4443c65',
                                                                                  'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
                                                                                  'sha256': '3db1965e25fbd2fe9ddf6b1af10ef1a47f479479e8a076646d6de46c3f7130b0'},
                                                                       'source_graph': {'bytes': 362316,
                                                                                        'commit': '9f2013ad9cb9caac9cec03cb213d9949c4443c65',
                                                                                        'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
                                                                                        'sha256': 'b56ca98e7c46d9e6ab9244b2fe32f15717db95a325a0ca5e52ee965d900f44c9'},
                                                                       'published_source_count': 360,
                                                                       'public_evidence': {'commit': 'e91af3a5c407bdeea243af7dd3c4248949d83e9b',
                                                                                           'path': 'docs/p1/20261125/p15-current-public-acceptance/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json',
                                                                                           'bytes': 11788,
                                                                                           'sha256': '1f2c0a0c1c00f3ac76eb2d0255ff480581438d624129f673b9f4e4e194ae37d7'},
                                                                       'evidence_kind': 'bounded_public_acceptance'},
                                                  'owned_count': 28,
                                                  'public_count': 28,
                                                  'audit_id': '2dd4c543e4398010981b'}}
SYNTHESIS_AC_PRIOR_RUNS = {'ImbalancedChen.P5OriginalSharpPrimeSynthesis': {'targets': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                                                  'accepted': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                                                  'reused': [],
                                                  'failed': [],
                                                  'not_accepted': [],
                                                  'not_started': [],
                                                  'readiness': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
                                                  'exit_code': 0,
                                                  'live_count': 112,
                                                  'result': {'bytes': 11872,
                                                             'sha256': '143b90e465f63ce485afde302aa66c4bf63f13d21d636e06862563848cbba92d'},
                                                  'worker': {'bytes': 11807,
                                                             'sha256': 'ceddbd34193c920757130eb916b20f933cf659b1932ee8e775d366ccc30fe556'},
                                                  'requested_targets': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis']}}
SYNTHESIS_AC_LATER_PINS = {'CONTEXT_AFTER.json': {'bytes': 524382,
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
                        'sha256': '35e5b2c76b05c53cc726c9cd12b0cb1dd660486a7a707346c7c1d2ed95771a12'},
 'executed-driver.py': {'bytes': 278990,
                        'sha256': '3db1965e25fbd2fe9ddf6b1af10ef1a47f479479e8a076646d6de46c3f7130b0'}}
SYNTHESIS_AC_LATER_TARGETS = ['ImbalancedChen.P5OriginalSharpPrimeSynthesis',
 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
SYNTHESIS_AC_LATER_RECORD = {'accepted_owners': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
 'all_selected_owners_accepted': False,
 'compiler_job': 'job_a108c4d7e2594e1fb5a674382db6600f',
 'dispatch_error': 'serialized worker exited 1',
 'evidence_bindings': {'CONTEXT_AFTER.json': {'bytes': 524382,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001/CONTEXT_AFTER.json',
                                              'sha256': 'c45a4363cc4bac2ff74740fcbc4e8c69a339b185cbba0e2cf9f67f9377cba257'},
                       'CONTEXT_BEFORE.json': {'bytes': 524382,
                                               'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001/CONTEXT_BEFORE.json',
                                               'sha256': 'c45a4363cc4bac2ff74740fcbc4e8c69a339b185cbba0e2cf9f67f9377cba257'},
                       'GIT_AFTER.json': {'bytes': 1157,
                                          'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001/GIT_AFTER.json',
                                          'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                       'GIT_BEFORE.json': {'bytes': 1157,
                                           'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001/GIT_BEFORE.json',
                                           'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                       'RESULT.json': {'bytes': 53836,
                                       'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001/RESULT.json',
                                       'sha256': 'f96f9bd0179d96a62d7e90c64b9c8b713d010ebda81088c539a917a83d851172'},
                       'WORKER_RESULT.json': {'bytes': 53720,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001/WORKER_RESULT.json',
                                              'sha256': '35e5b2c76b05c53cc726c9cd12b0cb1dd660486a7a707346c7c1d2ed95771a12'},
                       'executed-driver.py': {'bytes': 278990,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001/executed-driver.py',
                                              'sha256': '3db1965e25fbd2fe9ddf6b1af10ef1a47f479479e8a076646d6de46c3f7130b0'}},
 'failed_modules': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid'],
 'failure_messages': {'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': 'normal failed/scope differs: '
                                                                         'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'},
 'not_accepted_modules': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                          'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                          'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                          'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
 'not_started_modules': ['ImbalancedChen.P1OriginalSingletonAtlasTrim',
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
                                'ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
 'original_run': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00001',
 'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
 'source_commit': '9f2013ad9cb9caac9cec03cb213d9949c4443c65',
 'status': 'PARTIAL_FAILURE_AFTER_ACCEPTED_PREFIX',
 'targets': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis',
             'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
             'ImbalancedChen.P1OriginalSingletonAtlasTrim',
             'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
             'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
 'worker_exit_code': 1}
PREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS}


def synthesis_ac_prior_source_binding(s, graph, sources, module, prior):
    require(module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS and prior == SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS[module] and
            sources[module] == prior['source_sha256'] and
            len(s.h.closure(graph, [module])) == prior['live_source_closure_count'],
            'fixed Synthesis@AC prior source/own closure differs: ' + module)


def require_synthesis_ac_prior_scope(module, prior, public, original, worker):
    require(module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS and prior == SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS[module],
            'unknown or changed fixed Synthesis@AC prior')
    fixed, run_scope = prior['historical_group'], SYNTHESIS_AC_PRIOR_RUNS[module]
    expected = {
        'schema': 'p15_AC_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_AC_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': prior['source_commit'], 'source_anchor_commit': SYNTHESIS_AC_PRIOR_SOURCE_ANCHOR,
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
        'selected_owners_revalidated': list(SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS),
        'current_read_live_source_count': 112, 'current_read_preserved_dependency_count': 111,
        'owner_live_source_closure_count': prior['live_source_closure_count'],
        'source_runtime_and_original_receipts_unchanged': True, 'normal_or_kernel_commands_executed': 0,
        'types_or_archives_exported': False, 'axiom_union_exported': False,
        'new_lean_acceptance': False, 'whole_P1_5_complete': False,
        'stock_readiness_executed_by_collector': False,
        'later_same_source_reuse': SYNTHESIS_AC_LATER_RECORD,
    }
    require(all(public.get(key) == value and type(public.get(key)) is type(value)
                for key, value in expected.items()) and set(public['owners']) == {module},
            'fixed Synthesis@AC public identity/run/actual joint collection scope differs: ' + module)
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
            owner['later_same_AC_reuse_run'] == (str(base / 'runs/attempt-00001') if module == SYNTHESIS_AC_MODULE else None) and
            set(receipts) == set(paths) and all(valid_fingerprint(receipts[key]) for key in paths) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and valid_fingerprint(pair['before']) and
                pair['before'] == pair['after'] for pair in public['original_context_pairs'].values()),
            'fixed Synthesis@AC owner/count/six-receipt/context identity differs: ' + module)
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
                'fixed original AC RESULT/WORKER scope differs: ' + module)
    require(original['worker_exit_code'] == run_scope['exit_code'] and
            original['all_selected_owners_accepted'] is (run_scope['exit_code'] == 0) and
            'dispatch_error' not in worker and
            all(original[key] == worker[key] for key in ('targets', 'accepted_owners', 'failures',
                'acceptance_bindings', 'direct_import_readiness', 'original_supplier_acceptance_bindings')),
            'original AC RESULT/WORKER identity differs: ' + module)
    ready = original['direct_import_readiness'][module]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == [],
            'accepted Synthesis@AC owner direct-import readiness differs: ' + module)
    stock = public['original_final_stock_readiness']
    if run_scope['exit_code'] == 0:
        require('dispatch_error' not in original and original['final_stock_readiness'] == worker['final_stock_readiness'] and
                all(record['exit_code'] == 0 and record['actual_built_modules'] == [] and record['actual_failed_modules'] == []
                    for record in (stock, original['final_stock_readiness'])) and
                stock['recorded'] is True and stock['executed_again_by_collector'] is False and
                all(stock[key]['path'] == str(run / name) and valid_fingerprint({k: stock[key][k] for k in ('bytes', 'sha256')})
                    for key, name in (('command', 'final-stock-readiness-command.json'), ('log', 'final-stock-readiness.log'))),
                'original Synthesis successful final stock readiness differs')
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
            'Synthesis@AC public receipt paths/pins differ from original acceptance: ' + module)


def retained_synthesis_ac_prior_target(s, spec, module):
    require(module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS and module in spec.active and module not in spec.selected,
            'Synthesis@AC prior reuse is outside the actual dependency scope: ' + module)
    prior = spec.manifest['previously_accepted_targets'][module]
    synthesis_ac_prior_source_binding(s, spec.graph, spec.sources, module, prior)
    require(module not in spec.manifest['accepted_suppliers'] and prior['group'] not in spec.manifest['accepted_supplier_groups'],
            'Synthesis@AC prior overlay group collides: ' + module)
    fixed, run_scope = prior['historical_group'], SYNTHESIS_AC_PRIOR_RUNS[module]
    public = json.loads(published_binding(fixed['public_evidence']))
    base = Path(fixed['evidence_root']) / prior['source_commit']
    run = base / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', run_scope['result']))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', run_scope['worker']))
    require_synthesis_ac_prior_scope(module, prior, public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'original AC context/Git pair differs: ' + module)
    if run_scope['exit_code'] == 0:
        stock = original['final_stock_readiness']
        public_stock = public['original_final_stock_readiness']
        command = json.loads(retained_read(s, spec, run / 'final-stock-readiness-command.json',
                                         {k: public_stock['command'][k] for k in ('bytes', 'sha256')}))
        require(command == stock and stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + module + ':olean']) and
                stock['cwd'] == str(PROJECT) and stock['log'] == str(run / 'final-stock-readiness.log') and
                {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']} ==
                    {k: public_stock['log'][k] for k in ('bytes', 'sha256')},
                'original Synthesis guarded final stock command/log binding differs')
        retained_read(s, spec, Path(stock['log']), {k: public_stock['log'][k] for k in ('bytes', 'sha256')})
    later_run = base / 'runs/attempt-00001'
    require(retained_read(s, spec, later_run / 'executed-driver.py',
            SYNTHESIS_AC_LATER_PINS['executed-driver.py']) == published_binding(fixed['driver']),
            'original AC later executed driver differs')
    later = json.loads(retained_read(s, spec, later_run / 'RESULT.json', SYNTHESIS_AC_LATER_PINS['RESULT.json']))
    later_worker = json.loads(retained_read(s, spec, later_run / 'WORKER_RESULT.json', SYNTHESIS_AC_LATER_PINS['WORKER_RESULT.json']))
    for record in (later, later_worker):
        require(record['source_commit'] == prior['source_commit'] and
                record['targets'] == SYNTHESIS_AC_LATER_TARGETS and record['accepted_owners'] == [module] and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == 157 and
                set(record['direct_import_readiness']) == {SYNTHESIS_AC_FAILED_LOWERTRIM} and
                all(record[key] is False for key in ('whole_P1_complete', 'accepted_supplier_recompile_requested',
                    'dependency_rebuild_requested', 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error')) and
                record['reused_complete_selected_owners'] == [module] and
                record['failures'] == {SYNTHESIS_AC_FAILED_LOWERTRIM: 'normal failed/scope differs: ' + SYNTHESIS_AC_FAILED_LOWERTRIM} and
                set(record['acceptance_bindings']) == {module} and
                record['acceptance_bindings'][module] == original['acceptance_bindings'][module] and
                'final_stock_readiness' not in record and record['whole_P1_5_complete'] is False,
                'original AC later5 failure or Synthesis reuse identity differs')
    require(later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            later['dispatch_error'] == 'serialized worker exited 1' and
            all(later.get(key) == value for key, value in later_worker.items()),
            'original AC later5 RESULT/WORKER terminal status differs')
    for stem in ('CONTEXT', 'GIT'):
        require(retained_read(s, spec, later_run / (stem + '_BEFORE.json'), SYNTHESIS_AC_LATER_PINS[stem + '_BEFORE.json']) ==
                retained_read(s, spec, later_run / (stem + '_AFTER.json'), SYNTHESIS_AC_LATER_PINS[stem + '_AFTER.json']),
                'original AC later5 context/Git pair differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Synthesis@AC prior live source/full21 artifacts differ from original acceptance: ' + module)
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
            'Synthesis@AC prior full audit/count/source/full21 post-validation differs: ' + module)
    spec.dependency_pins[module] = expected
    return owner


