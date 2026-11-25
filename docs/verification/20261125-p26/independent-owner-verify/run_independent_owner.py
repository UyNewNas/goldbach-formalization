#!/usr/bin/env python3
"""Strict single-owner acceptance for five new source-only Saving19 interfaces.
The unchanged pinned Batch13 engine retains normal/kernel/all-owned audit.
No loader or ArchiveCore target; old facade credit retains its actual commit.
Preparing this file does not execute P1.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-p26-independent-owners-v1')
P1_BASE = '298670f119d24874b719facb3ef756f1e01223a1'
PREFIX = 'docs/verification/20261125-p26/independent-owner-verify/'
MANIFEST = PREFIX + 'SOURCE_TARGETS.json'
MANIFEST_SHA = '1366f95d28811c303f3a7d0f0079f1335752365251148cd041062a948a36746d'
OWNER_ORDER = ['ImbalancedChen.P2OriginalSaving19ArchiveSchema', 'ImbalancedChen.P2OriginalSaving19PrefixInterface', 'ImbalancedChen.P2OriginalSaving19PrefixMoments', 'ImbalancedChen.P2OriginalSaving19PullingFiniteCodes', 'ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix']
OWNERS = set(OWNER_ORDER)
FORBIDDEN_DEPENDENCIES = set(['ImbalancedChen.P2OriginalSaving19Archive', 'ImbalancedChen.P2OriginalSaving19ArchiveCore', 'ImbalancedChen.P2OriginalSaving19ArchivePackedInputs', 'ImbalancedChen.P2OriginalSaving19ArchivePackedLoader', 'ImbalancedChen.P2OriginalSaving19Original28918', 'ImbalancedChen.P2OriginalSaving19OwnedSource', 'ImbalancedChen.P2OriginalSaving19PullingReuse'])
CATALOG_COUNT = 231
REVIEW_INPUT_PINS = {'docs/verification/20261125-p26/independent-owner-verify/reviews/archive-schema-SOURCE_MANIFEST.json': 'cc65afc9a2c9cf1bbeeb50ff65812daa327791cb018b6ba50e059851331b01e4', 'docs/verification/20261125-p26/independent-owner-verify/reviews/moment-prefix-SOURCE_MANIFEST.json': 'c4ff339b84f337b089f5c40daaa46da7f689a015260a96bb948b6e2be4898ed7', 'docs/verification/20261125-p26/independent-owner-verify/reviews/pulling-reuse-SOURCE_MANIFEST.json': 'b14de157f4a82807ed4e58d821f13a86b893f48f119c90a93d5f1dbe14a6a449'}
LEGACY_HIGHER = {'owner': 'ImbalancedChen.P2OriginalSaving19HigherMoments', 'source_commit': 'bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3', 'source_sha256': '9b2253f2ae8174e6ab00fd60c276643823f947e75145ca23e00ec5ccd458524c', 'project_closure_count': 224, 'receipt_root': '/workspace/p1-complete-proof/20261125-p26-higher-facade-retry1/bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3/ImbalancedChen.P2OriginalSaving19HigherMoments', 'driver_path': 'docs/verification/20261125-p26/verify/run_higher_facade_retry1.py', 'driver_sha256': 'c7ffc22ec3f4cd453fd21a92814ead753cdb312c6a3bbedd814327e935ad607d', 'manifest_path': 'docs/verification/20261125-p26/SOURCE_FACADE_RETRY1.json', 'manifest_sha256': '798e79445595f9b3ae2c382a4d7ce42e6bcd0d58666d99f450a5b251c2d52dee', 'normal_path': 'normal/ImbalancedChen.P2OriginalSaving19HigherMoments/NORMAL_PASS.json', 'audit_directory': 'audits/b4796410e4ca5f3aac15', 'result_path': 'runs/attempt-00000/RESULT.json', 'receipt_pins': {'BINDING.json': {'bytes': 83955, 'sha256': 'd179cab2513fe99d60dfb36bbe728f7b7baa918dabbf3135425e7b85155cea35'}, 'normal/ImbalancedChen.P2OriginalSaving19HigherMoments/NORMAL_PASS.json': {'bytes': 119095, 'sha256': 'ecae4183471ccf0f315cea3eb319868c25e3239d81f66fa4e198cc83c14069e0'}, 'audits/b4796410e4ca5f3aac15/AUDIT_PLAN.json': {'bytes': 40047, 'sha256': '66059af109d45f9957cc83aed484c05097b743470c86d69437181d444f806af7'}, 'audits/b4796410e4ca5f3aac15/lane-0/VALIDATION_RESULTS.json': {'bytes': 32716, 'sha256': '12fc809c4fafe7f6b0f991dff8926539665418144e6a5415f72b53db913b4145'}, 'runs/attempt-00000/RESULT.json': {'bytes': 80139, 'sha256': 'ac489c0eb93da86ed757a572b8844d67ae38538809f2cd90b092702e8d969fd9'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json': {'bytes': 198662, 'sha256': 'facc63e5b5c804eb829c0a454c2fdd8a8f72689c472489457caab10326cf990a'}, 'runs/attempt-00000/P1_DEPENDENCY_CONTEXT_AFTER.json': {'bytes': 198662, 'sha256': 'facc63e5b5c804eb829c0a454c2fdd8a8f72689c472489457caab10326cf990a'}}, 'receipt_relabeling_allowed': False, 'recompile_or_reaudit_allowed': False}
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOL_SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
CONFIG_OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'
CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
EVIDENCE_PINS = {CONFIG_OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614', CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'}
CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)


def check_configs(project, configuration, d):
    need(all((project / p).is_file() and not (project / p).is_symlink() for p in CONFIGS) and
         {p: d.fingerprint(project / p) for p in CONFIGS} == configuration and
         not os.path.lexists(project / 'lakefile.lean'),
         'configuration differs from the selected pinned basis')


def source_origin(source_commit, module, h):
    path = h.module_path(module)
    return {'commit': source_commit, 'path': path}


def source_slot(project, module, payload, h, manifest):
    path = project / h.module_path(module)
    need(path.parent.is_dir() and not path.parent.is_symlink() and not path.is_symlink(),
         'target or target directory is a symlink or missing directory: ' + str(path))
    if not os.path.lexists(path):
        return {'exists': False, 'sha256': None, 'bytes': None, 'action': 'CREATE_NEW_ABSENT'}
    need(path.is_file(), 'target is not a regular file: ' + str(path))
    data = path.read_bytes()
    digest = sha(data)
    allowed = {sha(payload)} | set(manifest['modules'][module]['known_preimages'])
    need(digest in allowed, 'UNKNOWN_SOURCE_PREIMAGE ' + json.dumps(
        {'module': module, 'actual_sha256': digest, 'allowed_sha256': sorted(allowed)}, sort_keys=True))
    return {'exists': True, 'sha256': digest, 'bytes': len(data),
            'action': 'ALREADY_AFTER_NOOP' if digest == sha(payload) else 'INSTALL_BACKED_UP_PREIMAGE'}


def validate_manifest(manifest, module, h):
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



def inputs(args):
    need(re.fullmatch(r'[0-9a-f]{40}', args.source_commit) is not None,
         'source-commit must be a full lowercase Git SHA')
    need(subprocess.check_output(['git', 'cat-file', '-t', args.source_commit],
                                 cwd=args.source_repo).strip() == b'commit', 'source commit unavailable')
    need(subprocess.run(['git', 'merge-base', '--is-ancestor', P1_BASE, args.source_commit],
                        cwd=args.source_repo, check=False).returncode == 0,
         'source commit must descend from the reviewed P1 baseline')
    raw = {API_PATH: git(args.source_repo, API_COMMIT, API_PATH)}
    need(sha(raw[API_PATH]) == API_SHA, 'published Batch13 API pin differs')
    api = types.ModuleType('published_batch13_primitives')
    api.__file__ = '<pinned Git object: ' + API_PATH + '>'
    exec(compile(raw[API_PATH], api.__file__, 'exec'), api.__dict__)
    need(api.PROJECT == PROJECT and api.REPO == REPO and api.TOOLS == TOOL_SOURCE,
         'published helper environment differs')
    for path, digest in api.PINS.items():
        raw[path] = git(args.source_repo, TOOL_SOURCE, path)
        need(sha(raw[path]) == digest, 'unchanged helper pin differs: ' + path)
    for path, digest in EVIDENCE_PINS.items():
        raw[path] = git(args.source_repo, P1_BASE, path)
        need(sha(raw[path]) == digest, 'accepted configuration evidence differs: ' + path)
    h, ops, d = (api.load(raw[api.HELPER], 'batch5'), api.load(raw[api.OPS], 'batch6'),
                 api.load(raw[api.PRIMITIVES], 'snapshot_primitives'))
    for path, digest in REVIEW_INPUT_PINS.items():
        raw[path] = git(args.source_repo, args.source_commit, path)
        need(sha(raw[path]) == digest, 'reviewed Archive source manifest or public contract changed: ' + path)
    raw[MANIFEST] = git(args.source_repo, args.source_commit, MANIFEST)
    need(sha(raw[MANIFEST]) == MANIFEST_SHA, 'independent-owner strict target manifest pin differs')
    manifest = json.loads(raw[MANIFEST])
    validate_manifest(manifest, args.module, h)
    catalog = manifest['all_project_source_catalog']
    catalog_graph = {m: [x for x in row['imports'] if x.startswith('ImbalancedChen.')]
                     for m, row in catalog.items()}
    selected = h.closure(catalog_graph, [args.module])
    required = manifest['modules'][args.module]['required_accepted_owners']
    checked = h.closure(catalog_graph, [args.module, *required])
    all_graph, all_sources, payload = {}, {}, None
    for m in sorted(checked):
        origin = source_origin(args.source_commit, m, h)
        data = git(args.source_repo, origin['commit'], origin['path'])
        row = catalog[m]
        imports = h.imports(data)
        need(sha(data) == row['sha256'] and len(data) == row['bytes'] and imports == row['imports'],
             'reviewed project owner/dependency differs from frozen catalog: ' + m)
        all_sources[m] = sha(data)
        all_graph[m] = [x for x in imports if x.startswith('ImbalancedChen.')]
        if m == args.module:
            payload = data
            raw[origin['path']] = data
    graph = {m: all_graph[m] for m in sorted(selected)}
    sources = {m: all_sources[m] for m in sorted(selected)}
    need(payload is not None and len(graph) == manifest['modules'][args.module]['project_closure_count'] and
         not (FORBIDDEN_DEPENDENCIES & set(graph)), 'selected owner missing, wrong closure size, or forbidden production/data owner imported')
    h.closure(graph, [args.module])
    slot = source_slot(args.project, args.module, payload, h, manifest)
    differences = []
    for m in sorted(selected - {args.module}):
        actual_path = args.project / h.module_path(m)
        data = actual_path.read_bytes() if actual_path.is_file() and not actual_path.is_symlink() else None
        actual_sha = sha(data) if data is not None else None
        actual_imports = [x for x in h.imports(data) if x.startswith('ImbalancedChen.')] if data is not None else None
        if actual_sha != sources[m] or actual_imports != graph[m]:
            differences.append({'module': m, 'expected_source_commit': args.source_commit,
                                'expected_sha256': sources[m], 'actual_sha256': actual_sha,
                                'expected_imports': graph[m], 'actual_imports': actual_imports})
    need(not differences, 'COHERENT_P1_DEPENDENCY_CLOSURE_MISMATCH ' + json.dumps(differences, sort_keys=True))
    source_config = {}
    for path in CONFIGS:
        raw[path] = git(args.source_repo, args.source_commit, path)
        source_config[path] = {'bytes': len(raw[path]), 'sha256': sha(raw[path])}
    observed = json.loads(raw[CONFIG_OBSERVATION])['configs']
    review = json.loads(raw[CONFIG_REVIEW])
    runtime_config = review['runtime_configuration_bindings']
    need(review['source_configuration_bindings'] == source_config and
         runtime_config == {p: {k: observed[p][k] for k in ('bytes', 'sha256')} for p in CONFIGS} and
         all(observed[p]['exists'] and not observed[p]['is_symlink'] for p in CONFIGS) and
         not observed['lakefile.lean']['exists'] and not observed['lakefile.lean']['is_symlink'],
         'configuration observation/review binding differs')
    check_configs(args.project, source_config if args.config_basis == 'source' else runtime_config, d)
    if args.config_basis == 'runtime':
        need(d.runtime_binding(h) == review['existing_runtime_bindings'], 'accepted existing runtime differs')
    need(all(sha((args.project / h.module_path(m)).read_bytes()) == digest for m, digest in h.FOUR_ROOTS.items()),
         'protected original roots changed')
    provenance = {
        'schema': 'p26_independent_strict_single_owner_v1',
        'source_commit': args.source_commit, 'reviewed_p1_baseline': P1_BASE, 'module': args.module,
        'manifest_path': MANIFEST, 'manifest_sha256': sha(raw[MANIFEST]), 'manifest_owner_count': 5,
        'target_source_sha256': sources[args.module],
        'allowed_existing_target_sha256': sorted({sources[args.module]} |
                                                  set(manifest['modules'][args.module]['known_preimages'])),
        'all_project_sources_from_one_commit': True,
        'project_source_origins': {m: source_origin(args.source_commit, m, h) for m in sorted(sources)},
        'project_sources_after_single_target_install': sources,
        'source_closure_count': len(sources), 'project_import_graph': graph,
        'retained_dependencies_only_checked_for_readiness': sorted(selected - OWNERS),
        'required_preceding_strict_owners': required,
        'raw_fixture_reads_required': False,
        'legacy_higher_acceptance_required': manifest['modules'][args.module]['legacy_higher_acceptance_required'],
        'legacy_higher_source_commit': LEGACY_HIGHER['source_commit'] if manifest['modules'][args.module]['legacy_higher_acceptance_required'] else None,
        'old_receipts_relabeled': False,
        'old_core_224_exports_credit_transferred': False,
        'selected_independent_owner_only': True, 'archive_complete': False,
        'only_cell00_proved': False, 'proved_parse_cells': [],
        'archive_shape_or_row_guards_proved': False,
        'original_pulling_guards_proved': False, 'actual_row_numeric_or_floor_claim': False,
        'whole_P1_complete': False, 'whole_P2_complete': False,
    }
    return types.SimpleNamespace(api=api, h=h, ops=ops, d=d, raw=raw, payload=payload,
                                 graph=graph, sources=sources, provenance=provenance,
                                 all_graph=all_graph, all_sources=all_sources, manifest=manifest,
                                 source_config=source_config, runtime_config=runtime_config, slot=slot,
                                 source_commit=args.source_commit, source_repo=args.source_repo, module=args.module)


def binding(spec):
    return {**spec.provenance, 'project': str(PROJECT), 'api_commit': API_COMMIT,
            'tooling_commit': TOOL_SOURCE, 'input_sha256': {p: sha(b) for p, b in spec.raw.items()},
            'driver_sha256': sha(Path(__file__).read_bytes()), 'configuration_basis': 'runtime',
            'source_configuration': spec.source_config, 'runtime_configuration': spec.runtime_config,
            'runtime': spec.d.runtime_binding(spec.h)}


def install_one(spec, run):
    h, d, m = spec.h, spec.d, spec.module
    slot = source_slot(PROJECT, m, spec.payload, h, spec.manifest)
    d.save(run / 'SOURCE_PREFLIGHT_BEFORE.json', slot)
    path = h.module_path(m)
    if not slot['exists']:
        d.write_frozen(PROJECT / path, spec.payload)
        records = [{'module': m, 'path': path, 'actual_before_sha256': None,
                    'actual_after_sha256': sha((PROJECT / path).read_bytes()),
                    'mutated': True, 'action': 'CREATE_NEW_ABSENT'}]
    else:
        updates = [{'module': m, 'path': path, 'before_sha256': slot['sha256'],
                    'after_sha256': sha(spec.payload), 'cloud_source_mutation_required': False}]
        payloads = {path: spec.payload}
        spec.api.preflight_sources(PROJECT, updates, payloads, h)
        records = h.install_sources(PROJECT, updates, payloads, run / 'source-backups')
    need(sha((PROJECT / path).read_bytes()) == spec.sources[m], 'selected owner installation differs')
    d.save(run / 'SOURCE_INSTALL.json', {**spec.provenance, 'sources': records})


def check_installed(spec, runtime):
    check_configs(PROJECT, spec.runtime_config, spec.d)
    graph, actual = spec.h.project_graph(PROJECT, [spec.module])
    need(graph == spec.graph and {m: row['sha256'] for m, row in actual.items()} == spec.sources,
         'installed project source context changed')
    need(spec.d.runtime_binding(spec.h) == runtime, 'existing runtime changed')
    spec.h.check_roots()


def require_accepted_owners(spec, frozen):
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



def require_legacy_higher(spec, frozen):
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



def worker(spec, root, run):
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



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--module', choices=sorted(OWNERS), required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--config-basis', choices=('runtime', 'source'), default='runtime')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    args.source_repo, args.project = args.source_repo.resolve(), args.project.resolve()
    need(args.config_basis == 'runtime' or (args.check and args.project != PROJECT),
         'source configuration basis is limited to read-only local checks')
    if args.run:
        need(args.source_repo == REPO and args.project == PROJECT,
             'execution is restricted to the existing P1 cloud project/repository')
    spec = inputs(args)
    api, h, ops, d = spec.api, spec.h, spec.ops, spec.d
    root = ROOT / args.source_commit / args.module
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        print(json.dumps({**spec.provenance, 'target_installation_preflight': spec.slot,
              'status': 'SOURCE_CONFIG_ONLY_NOT_CLOUD_READY' if args.config_basis == 'source' else
                        'READ_ONLY_SOURCE_RUNTIME_CHECK_PASS_NOT_ACCEPTANCE',
              'source_installation_performed': False, 'cloud_compilation_performed': False}, sort_keys=True))
        return 0
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid run directory')
        return worker(spec, root, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(REPO)
    d.save(root / 'BINDING.json', binding(spec))
    for path, data in spec.raw.items():
        destination = ('source-configuration/' + path if path in CONFIGS else
                       'review-inputs/' + path if path in REVIEW_INPUT_PINS else
                       'e9.py' if path == api.E9 else Path(path).name)
        d.write_frozen(root / 'inputs' / destination, data)
    executed = root / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--source-commit', args.source_commit,
             '--module', args.module, '--run', '--inside-lane', '--run-dir', str(run)]
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(REPO)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty Git source worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
