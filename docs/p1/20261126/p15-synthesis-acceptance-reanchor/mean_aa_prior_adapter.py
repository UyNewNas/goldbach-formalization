

# Fixed Mean@AA acceptance; original AA later6 remains partial.
MEAN_AA_MODULE = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
MEAN_AA_FAILED_SYNTHESIS = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
MEAN_AA_PRIOR_SOURCE_ANCHOR = 'bde4a91307cb5e5872b6fc3c1e4a1520908b10c2'
MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS = {'ImbalancedChen.P5PrimeDivisorMeanCorrection': {'group': 'mean_aa',
                                                 'source_commit': 'ae373b971d2b88f97532dc883d835751dd10c67b',
                                                 'source_sha256': 'efb2138a0a1837c60ab5484afee7d884364dbf118f2753a3690881baebb4c02d',
                                                 'live_source_closure_count': 108,
                                                 'historical_group': {'source_commit': 'ae373b971d2b88f97532dc883d835751dd10c67b',
                                                                      'compiler_job': 'job_a01a8d1e8a7d4178988c0c0a5f296b6d',
                                                                      'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                                                                      'run': 'runs/attempt-00000',
                                                                      'owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                                                                      'driver': {'bytes': 251538,
                                                                                 'commit': 'ae373b971d2b88f97532dc883d835751dd10c67b',
                                                                                 'path': 'docs/p1/20261126/p15-current-corrections/run_selected.py',
                                                                                 'sha256': 'affa66215b9180e61052ba185f2502b5865416898bc8504b44175abe448bb074'},
                                                                      'source_graph': {'bytes': 359729,
                                                                                       'commit': 'ae373b971d2b88f97532dc883d835751dd10c67b',
                                                                                       'path': 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json',
                                                                                       'sha256': '39eaeca8207c7f387d6b5c6e44d85b38836c721c3c7b1cf1172bbe4c7f95d6c3'},
                                                                      'published_source_count': 360,
                                                                      'public_evidence': {'commit': '60e6b6e18fbda5f6b0e997d15392b32100e854d9',
                                                                                          'path': 'docs/p1/20261125/p15-current-public-acceptance/MEAN_AA_PUBLIC_ACCEPTANCE.json',
                                                                                          'bytes': 11979,
                                                                                          'sha256': '6d13eca3d7080946540ce94e98c169a2c38c1a5e7b0232294ae5557b67a5ced7'},
                                                                      'evidence_kind': 'bounded_public_acceptance'},
                                                 'owned_count': 22,
                                                 'public_count': 22,
                                                 'audit_id': '6f3e2f324ba32c191175'}}
MEAN_AA_PRIOR_RUNS = {'ImbalancedChen.P5PrimeDivisorMeanCorrection': {'targets': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                                                 'accepted': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                                                 'reused': [],
                                                 'failed': [],
                                                 'not_accepted': [],
                                                 'not_started': [],
                                                 'readiness': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
                                                 'exit_code': 0,
                                                 'live_count': 108,
                                                 'result': {'bytes': 8391,
                                                            'sha256': '6256690daae433327b6ef7543891ff829397bda1b15b92ae90096eb104bd9acb'},
                                                 'worker': {'bytes': 8326,
                                                            'sha256': '81e3d09172c6d6e4ba8fcb6af9979553c3b81cbcc22bff92c8b4774e838f2201'},
                                                 'requested_targets': ['ImbalancedChen.P5PrimeDivisorMeanCorrection']}}
MEAN_AA_LATER_PINS = {'CONTEXT_AFTER.json': {'bytes': 515448,
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
                        'sha256': '0bef1c288b0bfd2ee471667b383e09a1b1d6172946e2665b575753525cbf00c1'},
 'executed-driver.py': {'bytes': 251538,
                        'sha256': 'affa66215b9180e61052ba185f2502b5865416898bc8504b44175abe448bb074'}}
MEAN_AA_LATER_TARGETS = ['ImbalancedChen.P5PrimeDivisorMeanCorrection',
 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
MEAN_AA_LATER_RECORD = {'accepted_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
 'all_selected_owners_accepted': False,
 'compiler_job': 'job_2d377894edb64660880d7f3e8783b2ee',
 'dispatch_error': 'serialized worker exited 1',
 'evidence_bindings': {'CONTEXT_AFTER.json': {'bytes': 515448,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001/CONTEXT_AFTER.json',
                                              'sha256': '257662bbd5d7c94ec64762a9956bbfd75e3e8f1e41a982f3439f4873041b901b'},
                       'CONTEXT_BEFORE.json': {'bytes': 515448,
                                               'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001/CONTEXT_BEFORE.json',
                                               'sha256': '257662bbd5d7c94ec64762a9956bbfd75e3e8f1e41a982f3439f4873041b901b'},
                       'GIT_AFTER.json': {'bytes': 1157,
                                          'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001/GIT_AFTER.json',
                                          'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                       'GIT_BEFORE.json': {'bytes': 1157,
                                           'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001/GIT_BEFORE.json',
                                           'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                       'RESULT.json': {'bytes': 52166,
                                       'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001/RESULT.json',
                                       'sha256': 'cdc4c244088aaf3ca473a2d470c71bd303f72babb301246852e99ad6aa803230'},
                       'WORKER_RESULT.json': {'bytes': 52050,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001/WORKER_RESULT.json',
                                              'sha256': '0bef1c288b0bfd2ee471667b383e09a1b1d6172946e2665b575753525cbf00c1'},
                       'executed-driver.py': {'bytes': 251538,
                                              'path': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001/executed-driver.py',
                                              'sha256': 'affa66215b9180e61052ba185f2502b5865416898bc8504b44175abe448bb074'}},
 'failed_modules': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis'],
 'failure_messages': {'ImbalancedChen.P5OriginalSharpPrimeSynthesis': 'normal failed/scope differs: '
                                                                      'ImbalancedChen.P5OriginalSharpPrimeSynthesis'},
 'not_accepted_modules': ['ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                          'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                          'ImbalancedChen.P1OriginalSingletonAtlasTrim',
                          'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                          'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
 'not_started_modules': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
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
                                'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
                                'ImbalancedChen.P5PrimeDivisorMeanCorrection'],
 'original_run': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00001',
 'reused_complete_selected_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
 'source_commit': 'ae373b971d2b88f97532dc883d835751dd10c67b',
 'status': 'PARTIAL_FAILURE_AFTER_ACCEPTED_PREFIX',
 'targets': ['ImbalancedChen.P5PrimeDivisorMeanCorrection',
             'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
             'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
             'ImbalancedChen.P1OriginalSingletonAtlasTrim',
             'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
             'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
 'worker_exit_code': 1}
PREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS}


def mean_aa_prior_source_binding(s, graph, sources, module, prior):
    require(module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS and prior == MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS[module] and
            sources[module] == prior['source_sha256'] and
            len(s.h.closure(graph, [module])) == prior['live_source_closure_count'],
            'fixed Mean@AA prior source/own closure differs: ' + module)


def require_mean_aa_prior_scope(module, prior, public, original, worker):
    require(module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS and prior == MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS[module],
            'unknown or changed fixed Mean@AA prior')
    fixed, run_scope = prior['historical_group'], MEAN_AA_PRIOR_RUNS[module]
    expected = {
        'schema': 'p15_AA_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_AA_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': prior['source_commit'], 'source_anchor_commit': MEAN_AA_PRIOR_SOURCE_ANCHOR,
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
        'selected_owners_revalidated': list(MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS),
        'current_read_live_source_count': 108, 'current_read_preserved_dependency_count': 107,
        'owner_live_source_closure_count': prior['live_source_closure_count'],
        'source_runtime_and_original_receipts_unchanged': True, 'normal_or_kernel_commands_executed': 0,
        'types_or_archives_exported': False, 'axiom_union_exported': False,
        'new_lean_acceptance': False, 'whole_P1_5_complete': False,
        'stock_readiness_executed_by_collector': False,
        'later_same_source_reuse': MEAN_AA_LATER_RECORD,
    }
    require(all(public.get(key) == value and type(public.get(key)) is type(value)
                for key, value in expected.items()) and set(public['owners']) == {module},
            'fixed Mean@AA public identity/run/actual joint collection scope differs: ' + module)
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
            owner['later_same_AA_reuse_run'] == (str(base / 'runs/attempt-00001') if module == MEAN_AA_MODULE else None) and
            set(receipts) == set(paths) and all(valid_fingerprint(receipts[key]) for key in paths) and
            set(public['original_context_pairs']) == {'CONTEXT', 'GIT'} and
            all(set(pair) == {'before', 'after'} and valid_fingerprint(pair['before']) and
                pair['before'] == pair['after'] for pair in public['original_context_pairs'].values()),
            'fixed Mean@AA owner/count/six-receipt/context identity differs: ' + module)
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
                'fixed original AA RESULT/WORKER scope differs: ' + module)
    require(original['worker_exit_code'] == run_scope['exit_code'] and
            original['all_selected_owners_accepted'] is (run_scope['exit_code'] == 0) and
            'dispatch_error' not in worker and
            all(original[key] == worker[key] for key in ('targets', 'accepted_owners', 'failures',
                'acceptance_bindings', 'direct_import_readiness', 'original_supplier_acceptance_bindings')),
            'original AA RESULT/WORKER identity differs: ' + module)
    ready = original['direct_import_readiness'][module]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == [],
            'accepted Mean@AA owner direct-import readiness differs: ' + module)
    stock = public['original_final_stock_readiness']
    if run_scope['exit_code'] == 0:
        require('dispatch_error' not in original and original['final_stock_readiness'] == worker['final_stock_readiness'] and
                all(record['exit_code'] == 0 and record['actual_built_modules'] == [] and record['actual_failed_modules'] == []
                    for record in (stock, original['final_stock_readiness'])) and
                stock['recorded'] is True and stock['executed_again_by_collector'] is False and
                all(stock[key]['path'] == str(run / name) and valid_fingerprint({k: stock[key][k] for k in ('bytes', 'sha256')})
                    for key, name in (('command', 'final-stock-readiness-command.json'), ('log', 'final-stock-readiness.log'))),
                'original Mean successful final stock readiness differs')
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
            'Mean@AA public receipt paths/pins differ from original acceptance: ' + module)


def retained_mean_aa_prior_target(s, spec, module):
    require(module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS and module in spec.active and module not in spec.selected,
            'Mean@AA prior reuse is outside the actual dependency scope: ' + module)
    prior = spec.manifest['previously_accepted_targets'][module]
    mean_aa_prior_source_binding(s, spec.graph, spec.sources, module, prior)
    require(module not in spec.manifest['accepted_suppliers'] and prior['group'] not in spec.manifest['accepted_supplier_groups'],
            'Mean@AA prior overlay group collides: ' + module)
    fixed, run_scope = prior['historical_group'], MEAN_AA_PRIOR_RUNS[module]
    public = json.loads(published_binding(fixed['public_evidence']))
    base = Path(fixed['evidence_root']) / prior['source_commit']
    run = base / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', run_scope['result']))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', run_scope['worker']))
    require_mean_aa_prior_scope(module, prior, public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'original AA context/Git pair differs: ' + module)
    if run_scope['exit_code'] == 0:
        stock = original['final_stock_readiness']
        public_stock = public['original_final_stock_readiness']
        command = json.loads(retained_read(s, spec, run / 'final-stock-readiness-command.json',
                                         {k: public_stock['command'][k] for k in ('bytes', 'sha256')}))
        require(command == stock and stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + module + ':olean']) and
                stock['cwd'] == str(PROJECT) and stock['log'] == str(run / 'final-stock-readiness.log') and
                {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']} ==
                    {k: public_stock['log'][k] for k in ('bytes', 'sha256')},
                'original Mean guarded final stock command/log binding differs')
        retained_read(s, spec, Path(stock['log']), {k: public_stock['log'][k] for k in ('bytes', 'sha256')})
    later_run = base / 'runs/attempt-00001'
    require(retained_read(s, spec, later_run / 'executed-driver.py',
            MEAN_AA_LATER_PINS['executed-driver.py']) == published_binding(fixed['driver']),
            'original AA later executed driver differs')
    later = json.loads(retained_read(s, spec, later_run / 'RESULT.json', MEAN_AA_LATER_PINS['RESULT.json']))
    later_worker = json.loads(retained_read(s, spec, later_run / 'WORKER_RESULT.json', MEAN_AA_LATER_PINS['WORKER_RESULT.json']))
    for record in (later, later_worker):
        require(record['source_commit'] == prior['source_commit'] and
                record['targets'] == MEAN_AA_LATER_TARGETS and record['accepted_owners'] == [module] and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == 157 and
                set(record['direct_import_readiness']) == {MEAN_AA_FAILED_SYNTHESIS} and
                all(record[key] is False for key in ('whole_P1_complete', 'accepted_supplier_recompile_requested',
                    'dependency_rebuild_requested', 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error')) and
                record['reused_complete_selected_owners'] == [module] and
                record['failures'] == {MEAN_AA_FAILED_SYNTHESIS: 'normal failed/scope differs: ' + MEAN_AA_FAILED_SYNTHESIS} and
                set(record['acceptance_bindings']) == {module} and
                record['acceptance_bindings'][module] == original['acceptance_bindings'][module] and
                'final_stock_readiness' not in record and record['whole_P1_5_complete'] is False,
                'original AA later6 failure or Mean reuse identity differs')
    require(later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            later['dispatch_error'] == 'serialized worker exited 1' and
            all(later.get(key) == value for key, value in later_worker.items()),
            'original AA later6 RESULT/WORKER terminal status differs')
    for stem in ('CONTEXT', 'GIT'):
        require(retained_read(s, spec, later_run / (stem + '_BEFORE.json'), MEAN_AA_LATER_PINS[stem + '_BEFORE.json']) ==
                retained_read(s, spec, later_run / (stem + '_AFTER.json'), MEAN_AA_LATER_PINS[stem + '_AFTER.json']),
                'original AA later6 context/Git pair differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'Mean@AA prior live source/full21 artifacts differ from original acceptance: ' + module)
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
            'Mean@AA prior full audit/count/source/full21 post-validation differs: ' + module)
    spec.dependency_pins[module] = expected
    return owner


