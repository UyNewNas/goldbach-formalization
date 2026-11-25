def validate_manifest(manifest, module, h):
    need(manifest.get('schema') == 'p26_archive_core_continuation_targets_v1' and
         manifest.get('owners') == OWNER_ORDER and manifest.get('owner_count') == 2 and
         set(manifest.get('modules', {})) == OWNERS and module in OWNERS and
         manifest.get('review_input_pins') == REVIEW_INPUT_PINS and
         manifest.get('legacy_groups') == LEGACY_GROUPS and
         manifest.get('production_archive_allowed_sha256') == [ARCHIVE_SHA] and
         manifest.get('old_core_224_exports_credit_transferred') is False and
         manifest.get('old_receipts_relabeled') is False and
         manifest.get('archive_complete') is False,
         'continuation target scope or reviewed manifest differs')
    catalog = manifest.get('all_project_source_catalog', {})
    need(isinstance(catalog, dict) and len(catalog) == CATALOG_COUNT and
         OWNERS <= set(catalog) and not (FORBIDDEN_DEPENDENCIES & set(catalog)),
         'frozen continuation source catalog differs or includes a closed-guard owner')
    for m, row in catalog.items():
        need(row.get('path') == h.module_path(m) and row.get('source_path') == h.module_path(m) and
             re.fullmatch(r'[0-9a-f]{64}', row.get('sha256', '')) is not None and
             type(row.get('bytes')) is int and row['bytes'] > 0 and
             isinstance(row.get('imports'), list) and all(isinstance(x, str) for x in row['imports']),
             'frozen continuation project source differs: ' + m)
    graph = {m: [x for x in row['imports'] if x.startswith('ImbalancedChen.')]
             for m, row in catalog.items()}
    for m, row in manifest['modules'].items():
        closure = h.closure(graph, [m])
        expected_groups = ['v4_inputs', 'schema'] if m == CORE else ['schema']
        expected_owners = [x for group in expected_groups for x in LEGACY_GROUPS[group]['owners']]
        need(all(row.get(k) == catalog[m][k] for k in catalog[m]) and
             row.get('known_preimages') == ([CORE_PREIMAGE] if m == CORE else []) and
             row.get('target_absent_allowed') == (m != CORE) and
             row.get('project_closure_count') == (251 if m == CORE else 6) == len(closure) and
             row.get('required_legacy_groups') == expected_groups and
             row.get('required_legacy_owners') == expected_owners and
             set(expected_owners) <= closure and
             row.get('raw_fixture_reads_required') == (m == CORE),
             'continuation owner preimage, closure or legacy prerequisites differ: ' + m)
    need(len(manifest.get('original_loader_inputs', [])) == 26,
         'continuation must retain all original loader inputs')


def legacy_inputs(args, raw, h, manifest, selected):
    """Pin old driver/manifests and old Git sources without claiming receipt readiness."""
    result = {}
    catalog = manifest['all_project_source_catalog']
    for name in manifest['modules'][args.module]['required_legacy_groups']:
        desc = LEGACY_GROUPS[name]
        commit = desc['source_commit']
        for kind in ('driver', 'manifest'):
            data = git(args.source_repo, commit, desc[kind + '_path'])
            need(sha(data) == desc[kind + '_sha256'],
                 'actual legacy source evidence differs: ' + name + '/' + kind)
            raw['legacy-' + name + '-' + kind + ('.py' if kind == 'driver' else '.json')] = data
        old_manifest = json.loads(raw['legacy-' + name + '-manifest.json'])
        need(old_manifest['schema'] == desc['manifest_schema'] and
             old_manifest['owner_count'] == desc['manifest_owner_count'] and
             all(m in old_manifest['owners'] for m in desc['owners']) and
             CORE not in desc['owners'], 'legacy manifest scope differs: ' + name)
        old_catalog = old_manifest['all_project_source_catalog']
        old_graph = {m: [x for x in row['imports'] if x.startswith('ImbalancedChen.')]
                     for m, row in old_catalog.items()}
        old_closure = h.closure(old_graph, desc['owners'])
        need(old_closure <= selected, 'legacy closure is outside selected consumer: ' + name)
        differences = []
        for m in sorted(old_closure):
            row = old_catalog[m]
            data = git(args.source_repo, commit, h.module_path(m))
            imports = h.imports(data)
            need(sha(data) == row['sha256'] and len(data) == row['bytes'] and imports == row['imports'],
                 'legacy catalog is not its actual original Git source: ' + m)
            current = catalog[m]
            if any(current[k] != row[k] for k in ('bytes', 'sha256', 'imports')):
                differences.append({'module': m, 'legacy_commit': commit, 'legacy': row,
                                    'consumer_commit': args.source_commit, 'consumer': current})
        need(not differences, 'LEGACY_CROSS_COMMIT_SOURCE_OR_IMPORT_MISMATCH ' +
             json.dumps(differences, sort_keys=True))
        if name == 'v4_inputs':
            need(old_manifest['original_loader_inputs'] == manifest['original_loader_inputs'] and
                 old_manifest['production_archive_allowed_sha256'] == [ARCHIVE_SHA],
                 'legacy raw input or production Archive binding differs')
        result[name] = {'descriptor': desc, 'manifest': old_manifest,
                        'graph': old_graph, 'catalog': old_catalog}
    return result


def require_legacy_acceptance(spec, frozen, loader_current):
    """Validate every prior owner under its real old commit. Never build/audit one."""
    api, h, d = spec.api, spec.h, spec.d
    summaries = []
    for group_name in spec.manifest['modules'][spec.module]['required_legacy_groups']:
        group = spec.legacy[group_name]
        desc, old_manifest = group['descriptor'], group['manifest']
        old_commit = desc['source_commit']
        for module in desc['owners']:
            need(module != CORE, 'old ArchiveCore can never supply continuation credit')
            root = Path(desc['receipt_root']) / old_commit / module
            need(root.is_dir() and not root.is_symlink(), 'LEGACY_OWNER_NOT_READY ' + str(root))
            pinned = desc['known_receipt_pins'].get(module, {})
            for relative, expected in pinned.items():
                path = root / relative
                need(path.is_file() and not path.is_symlink() and d.fingerprint(path) == expected,
                     'known original receipt changed or missing: ' + str(path))
            prior_path = root / 'BINDING.json'
            need(prior_path.is_file() and not prior_path.is_symlink(),
                 'legacy original BINDING missing or not regular: ' + module)
            prior = api.read_json(prior_path)
            closure = h.closure(group['graph'], [module])
            graph = {m: group['graph'][m] for m in sorted(closure)}
            sources = {m: group['catalog'][m]['sha256'] for m in sorted(closure)}
            origins = {m: source_origin(old_commit, m, h) for m in sorted(closure)}
            need(prior.get('schema') == desc['binding_schema'] and
                 prior.get('source_commit') == old_commit and prior.get('module') == module and
                 prior.get('manifest_path') == desc['manifest_path'] and
                 prior.get('manifest_sha256') == desc['manifest_sha256'] and
                 prior.get('manifest_owner_count') == desc['manifest_owner_count'] and
                 prior.get('driver_sha256') == desc['driver_sha256'] and
                 prior.get('source_closure_count') == len(closure) and
                 prior.get('target_source_sha256') == sources[module] and
                 prior.get('project_import_graph') == graph and
                 prior.get('project_sources_after_single_target_install') == sources and
                 prior.get('project_source_origins') == origins and
                 prior.get('required_preceding_strict_owners') ==
                    old_manifest['modules'][module]['required_accepted_owners'] and
                 all(prior[k] == frozen[k] for k in ('project', 'runtime', 'runtime_configuration',
                    'source_configuration', 'configuration_basis', 'api_commit', 'tooling_commit')),
                 'legacy original binding or accepted runtime differs: ' + module)
            need({m: spec.sources[m] for m in closure} == sources and
                 {m: spec.graph[m] for m in closure} == graph,
                 'legacy source/import closure differs from consumer: ' + module)
            if group_name == 'v4_inputs':
                need(prior.get('loader_inputs') == loader_current == frozen['loader_inputs'] and
                     prior.get('production_archive_source') == frozen['production_archive_source'] and
                     prior.get('old_core_224_exports_credit_transferred') is False,
                     'legacy raw26 or unselected Archive source differs: ' + module)
            else:
                need(prior.get('raw_fixture_reads_required') is False and
                     prior.get('old_receipts_relabeled') is False,
                     'legacy Schema receipt scope differs')
            normal_path = root / 'normal' / module / 'NORMAL_PASS.json'
            need(normal_path.is_file() and not normal_path.is_symlink(),
                 'legacy normal receipt missing or not regular: ' + module)
            normal = api.read_json(normal_path)
            old_current = api.context(old_commit, PROJECT, module, graph, sources, h, d)
            api.normal_valid(old_commit, PROJECT, module, normal, old_current, h, d)
            accepted, audits = set(), []
            for directory in sorted((root / 'audits').glob('*')):
                need(directory.is_dir() and not directory.is_symlink() and
                     (directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                     'legacy partial audit requires inspection: ' + str(directory))
                plan_path = directory / 'AUDIT_PLAN.json'
                validation_path = directory / 'lane-0/VALIDATION_RESULTS.json'
                accepted.update(api.audit_valid(old_commit, PROJECT, directory,
                    api.read_json(plan_path), {module: normal}, graph, sources, h, d))
                audits.append({'plan': {'path': str(plan_path), **d.fingerprint(plan_path)},
                    'validation': {'path': str(validation_path), **d.fingerprint(validation_path)}})
            need(accepted == {module}, 'LEGACY_OWNER_LACKS_FULL_STRICT_ACCEPTANCE ' + module)
            successful = []
            for result_path in sorted((root / 'runs').glob('attempt-*/RESULT.json')):
                result = api.read_json(result_path)
                if result.get('status') != api.PASS or result.get('error') is not None:
                    continue
                need(result.get('schema') == desc['binding_schema'] and
                     result.get('source_commit') == old_commit and result.get('module') == module and
                     result.get('manifest_path') == desc['manifest_path'] and
                     result.get('manifest_sha256') == desc['manifest_sha256'] and
                     result.get('normal_passed') == [module] and
                     result.get('accepted_owners') == [module] and
                     result.get('all_selected_owners_accepted') is True and
                     result.get('accepted_for_actual_P1_context_only') is True and
                     result.get('project_source_origins') == origins and
                     result.get('project_sources_after_single_target_install') == sources and
                     result.get('project_import_graph') == graph and
                     all(result.get(k) is False for k in ('archive_complete', 'only_cell00_proved',
                         'archive_shape_or_row_guards_proved', 'whole_P1_complete', 'whole_P2_complete')),
                     'legacy original wrapper completion differs: ' + module)
                evidence = [result_path]
                for name in ('P1_DEPENDENCY_CONTEXT_BEFORE.json', 'P1_DEPENDENCY_CONTEXT_AFTER.json'):
                    path = result_path.parent / name
                    need(api.read_json(path)['context'] == old_current,
                         'legacy stored source/object/trace/config/runtime context changed: ' + module)
                    evidence.append(path)
                if group_name == 'v4_inputs':
                    need(result.get('loader_inputs') == loader_current and
                         result.get('production_archive_source') == frozen['production_archive_source'] and
                         result.get('old_core_224_exports_credit_transferred') is False,
                         'legacy wrapper raw26/Archive scope differs')
                    for name in ('LOADER_INPUTS_BEFORE.json', 'LOADER_INPUTS_AFTER.json'):
                        path = result_path.parent / name
                        need(api.read_json(path) == loader_current,
                             'legacy original raw26 path/bytes/hash snapshot differs: ' + module)
                        evidence.append(path)
                else:
                    need(result.get('old_receipts_relabeled') is False,
                         'legacy Schema completion has wrong receipt scope')
                successful.append([{'path': str(p), **d.fingerprint(p)} for p in evidence])
            need(successful, 'LEGACY_OWNER_LACKS_SUCCESSFUL_WRAPPER_CONTEXT ' + module)
            consumer_view = api.context(spec.source_commit, PROJECT, module, spec.graph, spec.sources, h, d)
            need({k: v for k, v in old_current.items() if k != 'source_commit'} ==
                 {k: v for k, v in consumer_view.items() if k != 'source_commit'},
                 'legacy/new consumer source/object/trace/config/runtime equivalence failed: ' + module)
            summaries.append({'legacy_group': group_name, 'legacy_owner': module,
                'legacy_source_commit': old_commit, 'consumer_source_commit': spec.source_commit,
                'receipt_root': str(root), 'binding': {'path': str(prior_path), **d.fingerprint(prior_path)},
                'normal_receipt': {'path': str(normal_path), **d.fingerprint(normal_path)},
                'audit_receipts': audits, 'successful_wrapper_runs': successful,
                'legacy_context_under_actual_commit': old_current,
                'consumer_view_of_same_closure': consumer_view,
                'legacy_source_plus_five_outputs': normal['source_plus_five_outputs'],
                'receipt_relabeled': False, 'recompiled': False, 'reaudited': False})
    need([r['legacy_owner'] for r in summaries] ==
         spec.provenance['required_legacy_owners'], 'legacy owner inventory incomplete')
    return summaries


def worker(spec, root, run):
    api, h, ops, d, m = spec.api, spec.h, spec.ops, spec.d, spec.module
    d.verify_lane(h)
    frozen = api.read_json(root / 'BINDING.json')
    need(frozen == binding(spec), 'serialized worker binding changed')
    passed, accepted, error, before = {}, set(), None, None
    legacy_before, loader_before = None, None
    try:
        if spec.provenance['raw_fixture_reads_required']:
            loader_before = loader_input_snapshot(PROJECT, d, spec.manifest['original_loader_inputs'])
            d.save(run / 'LOADER_INPUTS_BEFORE.json', loader_before)
            need(loader_before == frozen['loader_inputs'], 'raw26 changed before Core acceptance')
        legacy_before = require_legacy_acceptance(spec, frozen, loader_before)
        d.save(run / 'LEGACY_ACCEPTANCE_BEFORE.json', legacy_before)
        install_one(spec, run)
        check_installed(spec, frozen['runtime'])
        before = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_BEFORE.json', {'provenance': spec.provenance, 'context': before})
        passed[m] = api.normal_one(spec.source_commit, PROJECT, root, m, spec.graph, spec.sources, h, ops, d)
        api.audit(spec.source_commit, PROJECT, root, passed, spec.graph, spec.sources, h, ops, d, run, accepted)
    except Exception as caught:
        error = str(caught)
        ops.emit('P26_CORE_CONTINUATION_HELD_OR_FAILED', module=m, reason=error)
    try:
        check_installed(spec, frozen['runtime'])
        after = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_AFTER.json', {'provenance': spec.provenance, 'context': after})
        need(before is not None and after == before,
             'source/object/trace/configuration/runtime context changed during acceptance')
    except Exception as caught:
        message = str(caught)
        d.save(run / 'CONTEXT_AFTER_ERROR.json', {'error': message})
        error = message if error is None else error + '; POST_CONTEXT: ' + message
    loader_after = None
    try:
        if spec.provenance['raw_fixture_reads_required']:
            loader_after = loader_input_snapshot(PROJECT, d, spec.manifest['original_loader_inputs'])
            d.save(run / 'LOADER_INPUTS_AFTER.json', loader_after)
            need(loader_before == loader_after == frozen['loader_inputs'], 'raw26 changed during Core acceptance')
        legacy_after = require_legacy_acceptance(spec, frozen, loader_after)
        d.save(run / 'LEGACY_ACCEPTANCE_AFTER.json', legacy_after)
        need(legacy_before is not None and legacy_before == legacy_after,
             'original legacy receipts or context changed during selected acceptance')
    except Exception as caught:
        message = str(caught)
        d.save(run / 'LEGACY_OR_LOADER_AFTER_ERROR.json', {'error': message})
        error = message if error is None else error + '; POST_LEGACY_OR_RAW: ' + message
    complete = accepted == {m} and error is None
    result = {**spec.provenance, 'status': api.PASS if complete else 'HELD_OR_FAILED',
        'normal_passed': sorted(passed), 'accepted_owners': sorted(accepted), 'error': error,
        'accepted_for_actual_P1_context_only': complete, 'all_selected_owners_accepted': complete,
        'archive_complete': False, 'only_cell00_proved': False, 'proved_parse_cells': [],
        'archive_shape_or_row_guards_proved': False, 'actual_row_numeric_or_floor_claim': False,
        'old_core_224_exports_credit_transferred': False, 'old_receipts_relabeled': False}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0 if complete else 1
