#!/usr/bin/env python3
"""Build a source-only strict single-owner wrapper from reviewed wrappers."""
from pathlib import Path
import ast
import hashlib
import json
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
PROJECT_SOURCE = Path('/workspace/p26-source-closure')
REPO = Path('/workspace/p26-recovery')
V4 = Path('/workspace/p26-recovery-candidates/archive-v4/verify/run_archive_v4_inputs.py')
RETRY = PROJECT_SOURCE / 'docs/verification/20261125-p26/verify/run_higher_facade_retry1.py'
EVIDENCE = Path('/workspace/p26-facade-retry-evidence/facade-retry1/ImbalancedChen.P2OriginalSaving19HigherMoments')
PREFIX = 'docs/verification/20261125-p26/independent-owner-verify/'
ORDER = [
    'ImbalancedChen.P2OriginalSaving19ArchiveSchema',
    'ImbalancedChen.P2OriginalSaving19PrefixInterface',
    'ImbalancedChen.P2OriginalSaving19PrefixMoments',
    'ImbalancedChen.P2OriginalSaving19PullingFiniteCodes',
    'ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix',
]
LEGACY_COMMIT = 'bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3'
LEGACY_OWNER = 'ImbalancedChen.P2OriginalSaving19HigherMoments'
FORBIDDEN = [
    'ImbalancedChen.P2OriginalSaving19Archive',
    'ImbalancedChen.P2OriginalSaving19ArchiveCore',
    'ImbalancedChen.P2OriginalSaving19ArchivePackedInputs',
    'ImbalancedChen.P2OriginalSaving19ArchivePackedLoader',
    'ImbalancedChen.P2OriginalSaving19Original28918',
    'ImbalancedChen.P2OriginalSaving19OwnedSource',
    'ImbalancedChen.P2OriginalSaving19PullingReuse',
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fingerprint(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': sha(data)}


def function(source, name):
    return ast.get_source_segment(source, next(n for n in ast.parse(source).body
        if isinstance(n, ast.FunctionDef) and n.name == name))


def replace_once(source, before, after):
    assert source.count(before) == 1, before
    return source.replace(before, after)


def main():
    assert sha(V4.read_bytes()) == 'c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75'
    assert sha(RETRY.read_bytes()) == 'c7ffc22ec3f4cd453fd21a92814ead753cdb312c6a3bbedd814327e935ad607d'
    v4, retry = V4.read_text(), RETRY.read_text()
    helper = Path('/workspace/p26-recovery-candidates/archive-v4/verify/reference_batch5_source.py')
    pure = function(helper.read_text(), 'imports')
    ns = {'re': re}
    exec(compile(pure, '<existing pure imports lexer only>', 'exec'), ns)
    imports = ns['imports']
    catalog = {}

    def visit(module):
        if module in catalog:
            return
        path = module.replace('.', '/') + '.lean'
        data = (PROJECT_SOURCE / path).read_bytes()
        imps = imports(data)
        catalog[module] = {'path': path, 'source_path': path,
                           'bytes': len(data), 'sha256': sha(data), 'imports': imps}
        for dep in imps:
            if dep.startswith('ImbalancedChen.'):
                visit(dep)

    for module in ORDER:
        visit(module)
    assert not set(FORBIDDEN) & set(catalog)
    graph = {m: [x for x in r['imports'] if x.startswith('ImbalancedChen.')]
             for m, r in catalog.items()}

    def closure(module):
        seen = set()
        def rec(m):
            if m in seen:
                return
            seen.add(m)
            for d in graph[m]:
                rec(d)
        rec(module)
        return seen

    reviewed = {
        'archive-schema-SOURCE_MANIFEST.json': Path('/workspace/p26-recovery-candidates/archive-schema/SOURCE_MANIFEST.json'),
        'moment-prefix-SOURCE_MANIFEST.json': Path('/workspace/p26-recovery-candidates/moment-prefix-reuse/SOURCE_MANIFEST.json'),
        'pulling-reuse-SOURCE_MANIFEST.json': Path('/workspace/p26-recovery-candidates/pulling-reuse/SOURCE_MANIFEST.json'),
    }
    (HERE / 'reviews').mkdir(exist_ok=True)
    review_pins = {}
    for name, path in reviewed.items():
        shutil.copyfile(path, HERE / 'reviews' / name)
        review_pins[PREFIX + 'reviews/' + name] = sha(path.read_bytes())
    old = json.loads((EVIDENCE / 'BINDING.json').read_text())
    assert old['source_commit'] == LEGACY_COMMIT and old['module'] == LEGACY_OWNER
    assert old['target_source_sha256'] == '9b2253f2ae8174e6ab00fd60c276643823f947e75145ca23e00ec5ccd458524c'
    assert len(old['project_import_graph']) == len(old['project_sources_after_single_target_install']) == 224
    old_graph = old['project_import_graph']
    old_sources = old['project_sources_after_single_target_install']
    for module, digest in old_sources.items():
        assert catalog[module]['sha256'] == digest
        assert graph[module] == old_graph[module]
        blob = subprocess.check_output(['git', '-C', str(REPO), 'show', LEGACY_COMMIT + ':' + catalog[module]['path']])
        assert sha(blob) == digest and imports(blob) == catalog[module]['imports']
    receipt_paths = [
        'BINDING.json',
        'normal/' + LEGACY_OWNER + '/NORMAL_PASS.json',
        'audits/b4796410e4ca5f3aac15/AUDIT_PLAN.json',
        'audits/b4796410e4ca5f3aac15/lane-0/VALIDATION_RESULTS.json',
        'runs/attempt-00000/RESULT.json',
        'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json',
        'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json',
    ]
    legacy = {
        'owner': LEGACY_OWNER, 'source_commit': LEGACY_COMMIT,
        'source_sha256': old['target_source_sha256'], 'project_closure_count': 224,
        'receipt_root': '/workspace/p1-complete-proof/20261125-p26-higher-facade-retry1/' + LEGACY_COMMIT + '/' + LEGACY_OWNER,
        'driver_path': 'docs/verification/20261125-p26/verify/run_higher_facade_retry1.py',
        'driver_sha256': old['driver_sha256'],
        'manifest_path': old['manifest_path'], 'manifest_sha256': old['manifest_sha256'],
        'normal_path': receipt_paths[1], 'audit_directory': 'audits/b4796410e4ca5f3aac15',
        'result_path': receipt_paths[4], 'receipt_pins': {p: fingerprint(EVIDENCE / p) for p in receipt_paths},
        'receipt_relabeling_allowed': False, 'recompile_or_reaudit_allowed': False,
    }
    owners = {}
    for module in ORDER:
        deps = closure(module)
        owners[module] = {**catalog[module], 'known_preimages': [],
            'project_closure_count': len(deps),
            'required_accepted_owners': [m for m in ORDER if m != module and m in deps],
            'legacy_higher_acceptance_required': LEGACY_OWNER in deps}
    manifest = {
        'schema': 'p26_independent_strict_single_owner_targets_v1',
        'owner_count': len(ORDER), 'owners': ORDER, 'modules': owners,
        'all_project_source_catalog': dict(sorted(catalog.items())),
        'frozen_existing_module_count': len(catalog) - len(ORDER),
        'forbidden_project_dependencies': FORBIDDEN, 'review_input_pins': review_pins,
        'legacy_higher_acceptance': legacy,
        'old_v4_input_continuation': {
            'source_commit': '07826355aedef5a01e76c36ad304bc6b115f3c2b',
            'driver_sha256': 'c7d7a43bd0b4ebc52f6d884a4b83cc82de531157dffa435ee5234bfb15a02c75',
            'manifest_sha256': '29819ebed6b1a1ef036fd49f86db4e546cca74d93a73aa30f69d858908131f43',
            'last_owner': 'ImbalancedChen.P2OriginalSaving19ArchivePackedInputs',
            'skip_owner': 'ImbalancedChen.P2OriginalSaving19ArchiveCore',
            'execute_old_continuation_from_this_runner': False,
            'old_receipts_may_be_relabeled': False,
        },
        'raw_fixture_reads_required': False,
        'archive_complete': False, 'original_pulling_guards_proved': False,
        'actual_row_numeric_or_floor_claim': False,
    }
    payload = (json.dumps(manifest, indent=2) + '\n').encode()
    (HERE / 'SOURCE_TARGETS.json').write_bytes(payload)

    constants = '\n'.join([
        '#!/usr/bin/env python3',
        '"""Strict single-owner acceptance for five new source-only Saving19 interfaces.',
        'The unchanged pinned Batch13 engine retains normal/kernel/all-owned audit.',
        'No loader or ArchiveCore target; old facade credit retains its actual commit.',
        'Preparing this file does not execute P1.',
        '"""',
        'from pathlib import Path', 'import argparse', 'import hashlib', 'import json',
        'import os', 'import re', 'import subprocess', 'import sys', 'import types',
        '', 'sys.dont_write_bytecode = True',
        "PROJECT = Path('/workspace/blue-member-build')",
        "REPO = Path('/workspace/goldbach-formalization')",
        "ROOT = Path('/workspace/p1-complete-proof/20261125-p26-independent-owners-v1')",
        "P1_BASE = '298670f119d24874b719facb3ef756f1e01223a1'",
        'PREFIX = ' + repr(PREFIX),
        "MANIFEST = PREFIX + 'SOURCE_TARGETS.json'",
        'MANIFEST_SHA = ' + repr(sha(payload)),
        'OWNER_ORDER = ' + repr(ORDER), 'OWNERS = set(OWNER_ORDER)',
        'FORBIDDEN_DEPENDENCIES = set(' + repr(FORBIDDEN) + ')',
        'CATALOG_COUNT = ' + str(len(catalog)),
        'REVIEW_INPUT_PINS = ' + repr(review_pins),
        'LEGACY_HIGHER = ' + repr(legacy),
        "API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'",
        "API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'",
        "API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'",
        "TOOL_SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'",
        "CONFIG_OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'",
        "CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'",
        "EVIDENCE_PINS = {CONFIG_OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614', CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'}",
        "CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')",
    ])
    chunks = [constants]
    for name in ['need', 'sha', 'git', 'check_configs', 'source_origin', 'source_slot']:
        chunks.append(function(v4, name))
    chunks.append(VALIDATE_MANIFEST)
    inp = function(v4, 'inputs')
    inp = inp.replace("'Archive v4 strict target manifest pin differs'", "'independent-owner strict target manifest pin differs'")
    inp = inp.replace("FACADE not in graph, 'selected owner missing, wrong closure size, or closed-guard facade imported'", "not (FORBIDDEN_DEPENDENCIES & set(graph)), 'selected owner missing, wrong closure size, or forbidden production/data owner imported'")
    inp = replace_once(inp, "    production = production_archive_snapshot(args.project, d, manifest)\n    loader_inputs = loader_input_snapshot(args.project, d, manifest['original_loader_inputs'])\n", '')
    inp = inp.replace("'schema': 'p26_archive_v4_strict_single_input_owner_v1'", "'schema': 'p26_independent_strict_single_owner_v1'")
    inp = inp.replace("'manifest_owner_count': 32", "'manifest_owner_count': 5")
    inp = replace_once(inp, "        'production_archive_source': production,\n        'loader_inputs': loader_inputs,\n        'loader_input_identity_scope': 'all_26_actual_files_at_unchanged_original_loader_paths',\n", "        'raw_fixture_reads_required': False,\n        'legacy_higher_acceptance_required': manifest['modules'][args.module]['legacy_higher_acceptance_required'],\n        'legacy_higher_source_commit': LEGACY_HIGHER['source_commit'] if manifest['modules'][args.module]['legacy_higher_acceptance_required'] else None,\n        'old_receipts_relabeled': False,\n")
    inp = inp.replace("'selected_input_owner_only': True", "'selected_independent_owner_only': True")
    inp = inp.replace("'archive_shape_or_row_guards_proved': False,", "'archive_shape_or_row_guards_proved': False,\n        'original_pulling_guards_proved': False, 'actual_row_numeric_or_floor_claim': False,")
    inp = replace_once(inp, 'source_commit=args.source_commit, module=args.module)', 'source_commit=args.source_commit, source_repo=args.source_repo, module=args.module)')
    chunks.append(inp)
    chunks.append(function(v4, 'binding'))
    install = function(v4, 'install_one').replace("'cloud_source_mutation_required': m == CORE", "'cloud_source_mutation_required': False")
    chunks.append(install)
    chunks.append(function(retry, 'check_installed'))
    chunks.extend([REQUIRE_PRECEDING, REQUIRE_LEGACY, WORKER, function(v4, 'main')])
    chunks.append("if __name__ == '__main__':\n    raise SystemExit(main())")
    driver = '\n\n\n'.join(chunks) + '\n'
    ast.parse(driver)
    compile(driver, '<candidate syntax check only>', 'exec')
    (HERE / 'run_independent_owner.py').write_text(driver)
    checks = {'schema': 'p26_independent_owner_runner_static_v1',
        'driver': fingerprint(HERE / 'run_independent_owner.py'),
        'source_targets': fingerprint(HERE / 'SOURCE_TARGETS.json'),
        'reference_v4': {'path': str(V4), **fingerprint(V4)},
        'reference_retry': {'path': str(RETRY), **fingerprint(RETRY)},
        'source_commit_of_new_owners_fixed': False,
        'accepted_source_commit_runtime_parameter_required': True,
        'legacy_higher_224_sources_and_imports_match_actual_old_git_and_receipt': True,
        'owner_closure_counts': {m: r['project_closure_count'] for m, r in owners.items()},
        'syntax_parse_and_compile_code_object_only': True,
        'runner_or_compiler_executed': False,
        'unchanged_functions': []}
    for name in ['need','sha','git','check_configs','source_origin','source_slot','binding','main']:
        assert function(driver,name) == function(v4,name),name
        checks['unchanged_functions'].append(name)
    assert function(driver,'check_installed') == function(retry,'check_installed')
    checks['check_installed_exact_retry_reference'] = True
    (HERE / 'STATIC_AUDIT.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(json.dumps(checks, indent=2))


VALIDATE_MANIFEST = '''def validate_manifest(manifest, module, h):
    need(manifest.get('schema') == 'p26_independent_strict_single_owner_targets_v1' and
         manifest.get('owner_count') == 5 and manifest.get('owners') == OWNER_ORDER and
         set(manifest.get('modules', {})) == OWNERS and module in OWNERS and
         manifest.get('frozen_existing_module_count') == CATALOG_COUNT - 5 and
         set(manifest.get('forbidden_project_dependencies', [])) == FORBIDDEN_DEPENDENCIES and
         manifest.get('review_input_pins') == REVIEW_INPUT_PINS and
         manifest.get('legacy_higher_acceptance') == LEGACY_HIGHER and
         manifest.get('raw_fixture_reads_required') is False and
         manifest.get('archive_complete') is False and
         manifest.get('original_pulling_guards_proved') is False and
         manifest.get('actual_row_numeric_or_floor_claim') is False,
         'independent single-owner scope or reviewed manifest differs')
    catalog = manifest.get('all_project_source_catalog', {})
    need(isinstance(catalog, dict) and len(catalog) == CATALOG_COUNT and
         OWNERS <= set(catalog) and not (FORBIDDEN_DEPENDENCIES & set(catalog)),
         'frozen project source catalog differs or imports an excluded input/Core owner')
    for m, row in catalog.items():
        need(row.get('path') == h.module_path(m) and row.get('source_path') == h.module_path(m) and
             re.fullmatch(r'[0-9a-f]{64}', row.get('sha256', '')) is not None and
             type(row.get('bytes')) is int and row['bytes'] > 0 and
             isinstance(row.get('imports'), list) and all(isinstance(x, str) for x in row['imports']),
             'frozen project source record differs: ' + m)
    graph = {m: [d for d in r['imports'] if d.startswith('ImbalancedChen.')]
             for m, r in catalog.items()}
    for m, row in manifest['modules'].items():
        closure = h.closure(graph, [m])
        need(all(row.get(k) == catalog[m][k] for k in catalog[m]) and
             row.get('known_preimages') == [] and
             row.get('project_closure_count') == len(closure) and
             row.get('required_accepted_owners') == [x for x in OWNER_ORDER if x != m and x in closure] and
             all(OWNER_ORDER.index(x) < OWNER_ORDER.index(m) for x in row['required_accepted_owners']) and
             row.get('legacy_higher_acceptance_required') == (LEGACY_HIGHER['owner'] in closure),
             'owner preimage, closure or preceding acceptance differs: ' + m)
'''

REQUIRE_PRECEDING = '''def require_accepted_owners(spec, frozen):
    """Revalidate original same-commit receipts; no dependency compile/audit execution."""
    api, h, d = spec.api, spec.h, spec.d
    summaries = []
    for module in spec.provenance['required_preceding_strict_owners']:
        root = ROOT / spec.source_commit / module
        prior = api.read_json(root / 'BINDING.json')
        owners = h.closure(spec.all_graph, [module])
        graph = {m: spec.all_graph[m] for m in sorted(owners)}
        sources = {m: spec.all_sources[m] for m in sorted(owners)}
        origins = {m: source_origin(spec.source_commit, m, h) for m in sorted(owners)}
        need(prior['source_commit'] == spec.source_commit and prior['module'] == module and
             prior['project_sources_after_single_target_install'] == sources and
             prior['project_import_graph'] == graph and prior['project_source_origins'] == origins and
             all(prior[k] == frozen[k] for k in ('project', 'runtime', 'runtime_configuration',
                 'source_configuration', 'configuration_basis', 'manifest_path', 'manifest_sha256',
                 'manifest_owner_count', 'api_commit', 'tooling_commit', 'driver_sha256')),
             'preceding owner requires the same actual source and strict runtime: ' + module)
        normal_path = root / 'normal' / module / 'NORMAL_PASS.json'
        normal = api.read_json(normal_path)
        current = api.context(spec.source_commit, PROJECT, module, graph, sources, h, d)
        api.normal_valid(spec.source_commit, PROJECT, module, normal, current, h, d)
        accepted, audits = set(), []
        for directory in sorted((root / 'audits').glob('*')):
            need(directory.is_dir() and not directory.is_symlink() and
                 (directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                 'preceding owner partial audit requires inspection: ' + str(directory))
            accepted.update(api.audit_valid(spec.source_commit, PROJECT, directory,
                api.read_json(directory / 'AUDIT_PLAN.json'), {module: normal}, graph, sources, h, d))
            path = directory / 'lane-0/VALIDATION_RESULTS.json'
            audits.append({'path': str(path), **d.fingerprint(path)})
        need(accepted == {module}, 'preceding owner lacks complete strict acceptance: ' + module)
        successful = []
        for result_path in sorted((root / 'runs').glob('attempt-*/RESULT.json')):
            result = api.read_json(result_path)
            if result.get('status') != api.PASS or result.get('error') is not None:
                continue
            need(result['module'] == module and result['source_commit'] == spec.source_commit and
                 result['accepted_owners'] == [module] and result['all_selected_owners_accepted'] is True and
                 result['archive_complete'] is False and result['old_receipts_relabeled'] is False and
                 result['project_source_origins'] == origins and
                 result['project_sources_after_single_target_install'] == sources,
                 'preceding owner wrapper completion differs: ' + module)
            evidence = [result_path]
            for name in ('P1_DEPENDENCY_CONTEXT_BEFORE.json', 'P1_DEPENDENCY_CONTEXT_AFTER.json'):
                path = result_path.parent / name
                need(api.read_json(path)['context'] == current, 'preceding source/object context differs')
                evidence.append(path)
            successful.append([{'path': str(p), **d.fingerprint(p)} for p in evidence])
        need(successful, 'preceding owner has no complete successful wrapper record: ' + module)
        summaries.append({'module': module, 'source_commit': spec.source_commit,
            'recompiled': False, 'reaudited': False, 'normal_receipt': {
                'path': str(normal_path), **d.fingerprint(normal_path)},
            'audit_receipts': audits, 'successful_wrapper_runs': successful})
    return summaries
'''

REQUIRE_LEGACY = '''def require_legacy_higher(spec, frozen):
    """Verify bd718's actual receipt under bd718, then compare with the new consumer.

    The old receipt is never rewritten, reissued, or passed with a new commit.
    All original normal/full-owned validation still uses the pinned Batch13 API.
    """
    if not spec.provenance['legacy_higher_acceptance_required']:
        return None
    api, h, d = spec.api, spec.h, spec.d
    desc = spec.manifest['legacy_higher_acceptance']
    old_commit, module = desc['source_commit'], desc['owner']
    root = Path(desc['receipt_root'])
    receipt_records = {}
    for relative, expected in desc['receipt_pins'].items():
        path = root / relative
        need(path.is_file() and not path.is_symlink() and d.fingerprint(path) == expected,
             'published legacy facade receipt changed or missing: ' + str(path))
        receipt_records[relative] = {'path': str(path), **expected}
    for kind in ('driver', 'manifest'):
        data = git(spec.source_repo, old_commit, desc[kind + '_path'])
        need(sha(data) == desc[kind + '_sha256'], 'legacy facade source evidence differs: ' + kind)
    prior = api.read_json(root / 'BINDING.json')
    graph = prior['project_import_graph']
    sources = prior['project_sources_after_single_target_install']
    closure = h.closure(graph, [module])
    need(len(closure) == desc['project_closure_count'] and closure == set(graph) == set(sources) and
         prior['source_commit'] == old_commit and prior['module'] == module and
         prior['target_source_sha256'] == desc['source_sha256'] and
         prior['driver_sha256'] == desc['driver_sha256'] and
         prior['manifest_path'] == desc['manifest_path'] and
         prior['manifest_sha256'] == desc['manifest_sha256'] and
         all(prior[k] == frozen[k] for k in ('project', 'runtime', 'runtime_configuration',
             'source_configuration', 'configuration_basis', 'api_commit', 'tooling_commit')),
         'legacy facade context or accepted runtime identity differs')
    origins = {m: source_origin(old_commit, m, h) for m in sorted(closure)}
    need(prior['project_source_origins'] == origins, 'legacy original source origins differ')
    differences = []
    for m in sorted(closure):
        old_data = git(spec.source_repo, old_commit, h.module_path(m))
        old_imports = h.imports(old_data)
        need(sha(old_data) == sources[m] and
             [x for x in old_imports if x.startswith('ImbalancedChen.')] == graph[m],
             'legacy source does not match its original Git commit: ' + m)
        row = spec.manifest['all_project_source_catalog'].get(m)
        if row is None or row['sha256'] != sources[m] or row['bytes'] != len(old_data) or row['imports'] != old_imports:
            differences.append({'module': m, 'legacy_commit': old_commit, 'legacy_sha256': sources[m],
                'consumer_commit': spec.source_commit, 'consumer_catalog': row})
    need(not differences, 'LEGACY_FACADE_CROSS_COMMIT_SOURCE_OR_IMPORT_MISMATCH ' + json.dumps(differences, sort_keys=True))
    need({m: spec.sources[m] for m in closure} == sources and
         {m: spec.graph[m] for m in closure} == graph,
         'legacy closure differs from current exact consumer closure')
    old_current = api.context(old_commit, PROJECT, module, graph, sources, h, d)
    normal = api.read_json(root / desc['normal_path'])
    api.normal_valid(old_commit, PROJECT, module, normal, old_current, h, d)
    directory = root / desc['audit_directory']
    need(sorted(str(p.relative_to(root)) for p in (root / 'audits').iterdir()) == [desc['audit_directory']],
         'unexpected or partial legacy audit directory requires inspection')
    accepted = api.audit_valid(old_commit, PROJECT, directory,
        api.read_json(directory / 'AUDIT_PLAN.json'), {module: normal}, graph, sources, h, d)
    need(accepted == {module}, 'legacy facade full-owned acceptance is incomplete')
    result = api.read_json(root / desc['result_path'])
    need(result['status'] == api.PASS and result['error'] is None and
         result['source_commit'] == old_commit and result['module'] == module and
         result['accepted_owners'] == [module] and result['all_selected_owners_accepted'] is True and
         result['project_sources_after_single_target_install'] == sources and
         result['project_source_origins'] == origins,
         'legacy wrapper success is not the actual original accepted run')
    for relative in desc['receipt_pins']:
        if relative.endswith(('P1_DEPENDENCY_CONTEXT_BEFORE.json', 'P1_DEPENDENCY_CONTEXT_AFTER.json')):
            need(api.read_json(root / relative)['context'] == old_current,
                 'current legacy dependency objects/traces differ from accepted before/after context')
    consumer_view = api.context(spec.source_commit, PROJECT, module, spec.graph, spec.sources, h, d)
    need({k: v for k, v in old_current.items() if k != 'source_commit'} ==
         {k: v for k, v in consumer_view.items() if k != 'source_commit'},
         'cross-commit source/object/config/runtime equivalence failed')
    return {'legacy_owner': module, 'legacy_source_commit': old_commit,
        'consumer_source_commit': spec.source_commit, 'receipt_root': str(root),
        'receipt_fingerprints': receipt_records, 'legacy_context_under_its_actual_commit': old_current,
        'new_consumer_view_of_same_dependencies': consumer_view,
        'legacy_source_plus_five_outputs': normal['source_plus_five_outputs'],
        'source_and_imports_equivalent': True, 'objects_and_traces_equivalent': True,
        'receipt_relabeled': False, 'recompiled': False, 'reaudited': False}
'''

WORKER = '''def worker(spec, root, run):
    api, h, ops, d, m = spec.api, spec.h, spec.ops, spec.d, spec.module
    d.verify_lane(h)
    frozen = api.read_json(root / 'BINDING.json')
    need(frozen == binding(spec), 'serialized worker binding changed')
    passed, accepted, error, before = {}, set(), None, None
    reuse_before, legacy_before = None, None
    try:
        reuse_before = require_accepted_owners(spec, frozen)
        d.save(run / 'REUSED_PRECEDING_ACCEPTANCE_BEFORE.json', reuse_before)
        legacy_before = require_legacy_higher(spec, frozen)
        d.save(run / 'LEGACY_HIGHER_ACCEPTANCE_BEFORE.json', legacy_before)
        install_one(spec, run)
        check_installed(spec, frozen['runtime'])
        before = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_BEFORE.json', {'provenance': spec.provenance, 'context': before})
        passed[m] = api.normal_one(spec.source_commit, PROJECT, root, m, spec.graph, spec.sources, h, ops, d)
        api.audit(spec.source_commit, PROJECT, root, passed, spec.graph, spec.sources, h, ops, d, run, accepted)
    except Exception as caught:
        error = str(caught)
        ops.emit('P26_INDEPENDENT_OWNER_HELD_OR_FAILED', module=m, reason=error)
    try:
        check_installed(spec, frozen['runtime'])
        after = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_AFTER.json', {'provenance': spec.provenance, 'context': after})
        need(before is not None and after == before,
             'source/object/trace/configuration/runtime context changed during acceptance')
        reuse_after = require_accepted_owners(spec, frozen)
        d.save(run / 'REUSED_PRECEDING_ACCEPTANCE_AFTER.json', reuse_after)
        need(reuse_before == reuse_after, 'preceding accepted evidence changed during owner acceptance')
        legacy_after = require_legacy_higher(spec, frozen)
        d.save(run / 'LEGACY_HIGHER_ACCEPTANCE_AFTER.json', legacy_after)
        need(legacy_before == legacy_after, 'legacy facade evidence changed during owner acceptance')
    except Exception as caught:
        context_error = str(caught)
        d.save(run / 'CONTEXT_AFTER_ERROR.json', {'error': context_error})
        error = context_error if error is None else error + '; POST_CONTEXT: ' + context_error
    complete = accepted == {m} and error is None
    result = {**spec.provenance, 'status': api.PASS if complete else 'HELD_OR_FAILED',
        'normal_passed': sorted(passed), 'accepted_owners': sorted(accepted), 'error': error,
        'accepted_for_actual_P1_context_only': complete, 'all_selected_owners_accepted': complete,
        'archive_complete': False, 'only_cell00_proved': False,
        'proved_parse_cells': [], 'archive_shape_or_row_guards_proved': False,
        'original_pulling_guards_proved': False, 'actual_row_numeric_or_floor_claim': False,
        'old_receipts_relabeled': False}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0 if complete else 1
'''


if __name__ == '__main__':
    main()
