#!/usr/bin/env python3
"""Prepare a source-only strict continuation from the reviewed wrapper donors."""
from pathlib import Path
import ast
import hashlib
import json
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE = Path('/workspace/p26-source-closure')
REPO = Path('/workspace/p26-recovery')
INDEPENDENT = Path('/workspace/p26-recovery-candidates/independent-owner-verify/run_independent_owner.py')
V4 = Path('/workspace/p26-recovery-candidates/archive-v4/verify/run_archive_v4_inputs.py')
PREFIX = 'docs/verification/20261125-p26/archive-core-continuation/'
CORE = 'ImbalancedChen.P2OriginalSaving19ArchiveCore'
ROW = 'ImbalancedChen.P2OriginalSaving19RowNumerics'
SCHEMA = 'ImbalancedChen.P2OriginalSaving19ArchiveSchema'
ARCHIVE = 'ImbalancedChen.P2OriginalSaving19Archive'
ARCHIVE_SHA = 'f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49'
CORE_PREIMAGE = 'df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182'
ORDER = [CORE, ROW]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def fp(p):
    b = p.read_bytes()
    return {'bytes': len(b), 'sha256': sha(b)}


def git(commit, path):
    return subprocess.check_output(['git', '-C', str(REPO), 'show', commit + ':' + path])


def function(source, name):
    return ast.get_source_segment(source, next(n for n in ast.parse(source).body
        if isinstance(n, ast.FunctionDef) and n.name == name))


def once(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


def main():
    assert fp(INDEPENDENT)['sha256'] == 'a2f9528662278b6aa994fb160013b5d0c2f5d762a455dec536afa90004b8443e'
    assert fp(V4)['sha256'] == 'c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75'
    independent, v4 = INDEPENDENT.read_text(), V4.read_text()
    helper = Path('/workspace/p26-recovery-candidates/archive-v4/verify/reference_batch5_source.py')
    scope = {'re': re}
    exec(compile(function(helper.read_text(), 'imports'), '<existing pure imports lexer>', 'exec'), scope)
    imports = scope['imports']
    catalog = {}

    def visit(m):
        if m in catalog:
            return
        path = m.replace('.', '/') + '.lean'
        data = (SOURCE / path).read_bytes()
        imps = imports(data)
        catalog[m] = {'path': path, 'source_path': path, 'bytes': len(data),
                      'sha256': sha(data), 'imports': imps}
        for dep in imps:
            if dep.startswith('ImbalancedChen.'):
                visit(dep)

    for m in ORDER:
        visit(m)
    graph = {m: [x for x in r['imports'] if x.startswith('ImbalancedChen.')]
             for m, r in catalog.items()}

    def closure(g, roots):
        seen = set()
        def go(m):
            if m in seen:
                return
            seen.add(m)
            for d in g[m]:
                go(d)
        for m in roots:
            go(m)
        return seen

    assert len(catalog) == 252 and len(closure(graph, [CORE])) == 251
    assert len(closure(graph, [ROW])) == 6
    assert catalog[CORE]['sha256'] == '4f5fcde939aad232d55f846ba5b52ca44862085cdf3354a288d354b953138c03'
    assert catalog[ROW]['sha256'] == '4be5f94041cc77997b8ad720966bc87938824493287480dd13d8abc7d95ef98e'
    forbidden = [ARCHIVE, 'ImbalancedChen.P2OriginalSaving19Original28918',
                 'ImbalancedChen.P2OriginalSaving19OwnedSource', 'ImbalancedChen.P2OriginalSaving19PullingReuse']
    assert not set(forbidden) & set(catalog)
    groups = {
        'v4_inputs': {
            'source_commit': '07826355aedef5a01e76c36ad304bc6b115f3c2b',
            'driver_path': 'docs/verification/20261125-p26/archive-v4/verify/run_archive_v4_inputs.py',
            'driver_sha256': fp(V4)['sha256'],
            'manifest_path': 'docs/verification/20261125-p26/archive-v4/verify/SOURCE_TARGETS.json',
            'manifest_sha256': '29819ebed6b1a1ef036fd49f86db4e546cca74d93a73aa30f69d858908131f43',
            'manifest_schema': 'p26_archive_v4_strict_input_targets_v1',
            'manifest_owner_count': 32,
            'binding_schema': 'p26_archive_v4_strict_single_input_owner_v1',
            'receipt_root': '/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1',
        },
        'schema': {
            'source_commit': '77c23a2a530ce8d34ec79f88181817072024d4a9',
            'driver_path': 'docs/verification/20261125-p26/independent-owner-verify/run_independent_owner.py',
            'driver_sha256': fp(INDEPENDENT)['sha256'],
            'manifest_path': 'docs/verification/20261125-p26/independent-owner-verify/SOURCE_TARGETS.json',
            'manifest_sha256': '1366f95d28811c303f3a7d0f0079f1335752365251148cd041062a948a36746d',
            'manifest_schema': 'p26_independent_strict_single_owner_targets_v1',
            'manifest_owner_count': 5,
            'binding_schema': 'p26_independent_strict_single_owner_v1',
            'receipt_root': '/workspace/p1-complete-proof/20261125-p26-independent-owners-v1',
        },
    }
    old_manifests = {}
    equivalence = {}
    for name, desc in groups.items():
        for kind in ('driver', 'manifest'):
            assert sha(git(desc['source_commit'], desc[kind + '_path'])) == desc[kind + '_sha256']
        old = json.loads(git(desc['source_commit'], desc['manifest_path']))
        old_manifests[name] = old
        desc['owners'] = [m for m in old['owners'] if m != CORE] if name == 'v4_inputs' else [SCHEMA]
        assert len(desc['owners']) == (31 if name == 'v4_inputs' else 1)
        old_graph = {m: [x for x in row['imports'] if x.startswith('ImbalancedChen.')]
                     for m, row in old['all_project_source_catalog'].items()}
        old_closure = closure(old_graph, desc['owners'])
        for m in old_closure:
            row = old['all_project_source_catalog'][m]
            data = git(desc['source_commit'], m.replace('.', '/') + '.lean')
            assert sha(data) == row['sha256'] and len(data) == row['bytes'] and imports(data) == row['imports']
            assert all(catalog[m][k] == row[k] for k in ('bytes', 'sha256', 'imports'))
        equivalence[name] = {'actual_old_git_sources_compared': len(old_closure),
                             'all_source_bytes_and_full_imports_equal': True}
        desc['known_receipt_pins'] = {}
    first7 = Path('/workspace/p26-v4-first7-evidence/archive-v4-first7')
    for owner in sorted(first7.iterdir()):
        if not owner.is_dir():
            continue
        module = owner.name
        assert module in groups['v4_inputs']['owners']
        binding = json.loads((owner / 'BINDING.json').read_text())
        assert binding['source_commit'] == groups['v4_inputs']['source_commit']
        assert binding['driver_sha256'] == groups['v4_inputs']['driver_sha256']
        paths = [owner / 'BINDING.json', owner / 'normal' / module / 'NORMAL_PASS.json']
        for audit in sorted((owner / 'audits').iterdir()):
            paths += [audit / 'AUDIT_PLAN.json', audit / 'lane-0/VALIDATION_RESULTS.json']
        for result in sorted((owner / 'runs').glob('attempt-*/RESULT.json')):
            j = json.loads(result.read_text())
            if j.get('status') != 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS' or j.get('error') is not None:
                continue
            paths.append(result)
            paths += [result.parent / x for x in ['P1_DEPENDENCY_CONTEXT_BEFORE.json',
                'P1_DEPENDENCY_CONTEXT_AFTER.json', 'LOADER_INPUTS_BEFORE.json', 'LOADER_INPUTS_AFTER.json']]
        groups['v4_inputs']['known_receipt_pins'][module] = {p.relative_to(owner).as_posix(): fp(p) for p in paths}
    assert len(groups['v4_inputs']['known_receipt_pins']) == 7
    reviews = {
        'archive-schema-SOURCE_MANIFEST.json': Path('/workspace/p26-recovery-candidates/archive-schema/SOURCE_MANIFEST.json'),
        'row-numerics-SOURCE_MANIFEST.json': Path('/workspace/p26-recovery-candidates/row-numerics/SOURCE_MANIFEST.json'),
    }
    (HERE / 'reviews').mkdir(exist_ok=True)
    pins = {}
    for name, p in reviews.items():
        shutil.copyfile(p, HERE / 'reviews' / name)
        pins[PREFIX + 'reviews/' + name] = sha(p.read_bytes())
    owners = {}
    for m in ORDER:
        selected_groups = ['v4_inputs', 'schema'] if m == CORE else ['schema']
        owners[m] = {**catalog[m], 'known_preimages': [CORE_PREIMAGE] if m == CORE else [],
            'target_absent_allowed': m != CORE, 'project_closure_count': len(closure(graph, [m])),
            'required_legacy_groups': selected_groups,
            'required_legacy_owners': [x for g in selected_groups for x in groups[g]['owners']],
            'raw_fixture_reads_required': m == CORE}
    manifest = {'schema': 'p26_archive_core_continuation_targets_v1', 'owner_count': 2,
        'owners': ORDER, 'modules': owners, 'all_project_source_catalog': dict(sorted(catalog.items())),
        'legacy_groups': groups, 'review_input_pins': pins,
        'original_loader_inputs': old_manifests['v4_inputs']['original_loader_inputs'],
        'production_archive_allowed_sha256': [ARCHIVE_SHA],
        'old_core_224_exports_credit_transferred': False, 'old_receipts_relabeled': False,
        'archive_complete': False}
    (HERE / 'SOURCE_TARGETS.json').write_text(json.dumps(manifest, indent=2) + '\n')
    constants = independent[:independent.index('\ndef need')]
    constants = constants[constants.index('from pathlib import Path'):]
    constants = constants[:constants.index('ROOT =')] + constants[constants.index('ROOT ='):]
    constants = once(constants, "ROOT = Path('/workspace/p1-complete-proof/20261125-p26-independent-owners-v1')",
                     "ROOT = Path('/workspace/p1-complete-proof/20261125-p26-core-continuation-v1')")
    constants = once(constants, "PREFIX = 'docs/verification/20261125-p26/independent-owner-verify/'", 'PREFIX = ' + repr(PREFIX))
    constants = re.sub(r'^MANIFEST_SHA = .*$', 'MANIFEST_SHA = ' + repr(sha((HERE / 'SOURCE_TARGETS.json').read_bytes())), constants, flags=re.M)
    constants = re.sub(r'^OWNER_ORDER = .*$', 'OWNER_ORDER = ' + repr(ORDER), constants, flags=re.M)
    constants = re.sub(r'^FORBIDDEN_DEPENDENCIES = .*$', 'FORBIDDEN_DEPENDENCIES = set(' + repr(forbidden) + ')', constants, flags=re.M)
    constants = re.sub(r'^CATALOG_COUNT = .*$', 'CATALOG_COUNT = 252', constants, flags=re.M)
    constants = re.sub(r'^REVIEW_INPUT_PINS = .*$', 'REVIEW_INPUT_PINS = ' + repr(pins), constants, flags=re.M)
    constants = re.sub(r'^LEGACY_HIGHER = .*$', 'LEGACY_GROUPS = ' + repr(groups) + '\nCORE = ' + repr(CORE) + '\nCORE_PREIMAGE = ' + repr(CORE_PREIMAGE) + '\nARCHIVE_SHA = ' + repr(ARCHIVE_SHA), constants, flags=re.M)
    functions = (HERE / 'continuation_functions.py.inc').read_text()
    validate = function(functions, 'validate_manifest')
    legacy_inputs = function(functions, 'legacy_inputs')
    legacy_acceptance = function(functions, 'require_legacy_acceptance')
    worker = function(functions, 'worker')
    inputs = function(independent, 'inputs')
    inputs = once(inputs, "manifest['modules'][args.module]['required_accepted_owners']", "manifest['modules'][args.module]['required_legacy_owners']")
    inputs = once(inputs, "    slot = source_slot(args.project, args.module, payload, h, manifest)",
        "    legacy = legacy_inputs(args, raw, h, manifest, selected)\n    slot = source_slot(args.project, args.module, payload, h, manifest)\n    need(args.module != CORE or slot['exists'], 'Core requires the known existing old v2 or exact new source slot')")
    inputs = inputs[:inputs.index('    provenance = {')] + '''    production = production_archive_snapshot(args.project, d, manifest)
    loader_inputs = (loader_input_snapshot(args.project, d, manifest['original_loader_inputs'])
                     if manifest['modules'][args.module]['raw_fixture_reads_required'] else None)
    provenance = {
        'schema': 'p26_core_continuation_strict_single_owner_v1',
        'source_commit': args.source_commit, 'reviewed_p1_baseline': P1_BASE, 'module': args.module,
        'manifest_path': MANIFEST, 'manifest_sha256': sha(raw[MANIFEST]), 'manifest_owner_count': 2,
        'target_source_sha256': sources[args.module],
        'allowed_existing_target_sha256': sorted({sources[args.module]} |
            set(manifest['modules'][args.module]['known_preimages'])),
        'all_project_sources_from_one_commit': True,
        'project_source_origins': {m: source_origin(args.source_commit, m, h) for m in sorted(sources)},
        'project_sources_after_single_target_install': sources,
        'source_closure_count': len(sources), 'project_import_graph': graph,
        'retained_dependencies_only_checked_for_readiness': sorted(selected - OWNERS - set(required)),
        'required_legacy_owners': required,
        'legacy_source_commits': {g: LEGACY_GROUPS[g]['source_commit'] for g in legacy},
        'legacy_receipts_validated_during_readonly_preflight': False,
        'production_archive_source': production, 'loader_inputs': loader_inputs,
        'raw_fixture_reads_required': manifest['modules'][args.module]['raw_fixture_reads_required'],
        'loader_input_identity_scope': 'all_26_original_paths_bytes_sha' if loader_inputs is not None else 'not_applicable_no_raw_file_reads',
        'selected_owner_only': True, 'old_core_224_exports_credit_transferred': False,
        'old_receipts_relabeled': False, 'archive_complete': False, 'only_cell00_proved': False,
        'proved_parse_cells': [], 'archive_shape_or_row_guards_proved': False,
        'actual_row_numeric_or_floor_claim': False, 'whole_P1_complete': False, 'whole_P2_complete': False,
    }
    return types.SimpleNamespace(api=api, h=h, ops=ops, d=d, raw=raw, payload=payload,
        graph=graph, sources=sources, provenance=provenance, all_graph=all_graph,
        all_sources=all_sources, manifest=manifest, legacy=legacy, source_config=source_config,
        runtime_config=runtime_config, slot=slot, source_commit=args.source_commit,
        source_repo=args.source_repo, module=args.module)'''
    install = function(v4, 'install_one')
    install = once(install, "    d.save(run / 'SOURCE_PREFLIGHT_BEFORE.json', slot)",
        "    need(m != CORE or slot['exists'], 'Core cannot be created in an absent source slot')\n    d.save(run / 'SOURCE_PREFLIGHT_BEFORE.json', slot)")
    preserved = [function(independent, x) for x in ['need', 'sha', 'git', 'check_configs', 'source_origin', 'source_slot']]
    parts = [constants, *preserved, validate, function(v4, 'production_archive_snapshot'),
        function(v4, 'loader_input_snapshot'), legacy_inputs, inputs, function(independent, 'binding'),
        install, function(v4, 'check_installed'), legacy_acceptance, worker, function(independent, 'main')]
    driver = '#!/usr/bin/env python3\n"""Strict single-owner new Core or RowNumerics acceptance, reusing actual old receipts.\nNo old Core build, prerequisite rebuild, receipt relabeling or invented readiness.\nThis candidate is source-only until Root publishes and runs it.\n"""\n' + '\n\n\n'.join(parts) + "\n\nif __name__ == '__main__':\n    raise SystemExit(main())\n"
    ast.parse(driver)
    compile(driver, '<unexecuted continuation candidate>', 'exec')
    (HERE / 'run_archive_core_continuation.py').write_text(driver)
    static = {'schema': 'p26_core_continuation_static_preparation_v1',
        'driver': fp(HERE / 'run_archive_core_continuation.py'),
        'manifest': fp(HERE / 'SOURCE_TARGETS.json'), 'legacy_source_equivalence': equivalence,
        'known_actual_receipt_owners': sorted(groups['v4_inputs']['known_receipt_pins']),
        'pending_receipts_not_invented': 25,
        'source_commit_for_new_targets_fixed': False,
        'new_owner_closures': {m: len(closure(graph, [m])) for m in ORDER},
        'driver_executed': False, 'P1_submitted': False, 'compiler_executed': False,
        'unchanged_functions': ['need', 'sha', 'git', 'check_configs', 'source_origin', 'source_slot',
            'production_archive_snapshot', 'loader_input_snapshot', 'binding', 'check_installed', 'main']}
    for name in static['unchanged_functions']:
        donor = v4 if name in ['production_archive_snapshot', 'loader_input_snapshot', 'check_installed'] else independent
        assert function(driver, name) == function(donor, name)
    (HERE / 'STATIC_AUDIT.json').write_text(json.dumps(static, indent=2) + '\n')
    print(json.dumps(static, indent=2))


if __name__ == '__main__':
    main()
