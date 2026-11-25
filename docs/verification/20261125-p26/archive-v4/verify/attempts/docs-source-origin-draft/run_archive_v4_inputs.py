#!/usr/bin/env python3
"""Strict acceptance candidate for the 32 Saving19 Archive v4 input owners.

Only --module is installed/normal-built. The published Batch13 engine and its
normal/context/audit checks, Batch5 helpers, lane-0 serializer and accepted
runtime review are unchanged. All 26 original raw files are fingerprinted and
compared with the reviewed metadata before and after each selected owner run.
The original closed-guard Archive facade is not an executable target here.
This file is a source candidate; preparing it does not execute P1.
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
ROOT = Path('/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1')
P1_BASE = '298670f119d24874b719facb3ef756f1e01223a1'
PREFIX = 'docs/verification/20261125-p26/archive-v4/'
MANIFEST = PREFIX + 'verify/SOURCE_TARGETS.json'
MANIFEST_SHA = 'bb43f20bc9084ede6dcbe4ab5359d4932cc1935301e4a0f798b09465194f7f92'
CORE = 'ImbalancedChen.P2OriginalSaving19ArchiveCore'
FACADE = 'ImbalancedChen.P2OriginalSaving19Archive'
READER = 'ImbalancedChen.P2OriginalSaving19SourceJson'
CORE_PREIMAGE = 'df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182'
OWNER_ORDER = ['ImbalancedChen.P2OriginalSaving19PackedChars', 'ImbalancedChen.P2OriginalSaving19CharInputBridge', 'ImbalancedChen.P2OriginalSaving19SourceJsonCharInput', 'ImbalancedChen.P2OriginalSaving19ArchivePackedLoader', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData12', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData01', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData02', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData03', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData04', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData06', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData07', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData08', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData09', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData10', 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData11', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData00', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData01', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData02', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData03', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData04', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData05', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData06', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData07', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData08', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData09', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData10', 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData11', 'ImbalancedChen.P2OriginalSaving19ArchivePackedInputs', 'ImbalancedChen.P2OriginalSaving19ArchiveCore']
OWNERS = set(OWNER_ORDER)
REVIEW_INPUT_PINS = {'docs/verification/20261125-p26/archive-v4/SOURCE_MANIFEST.json': 'c11effc98bbf61da960ebd91e28343f643e3865ed7ee9ab194fb4d1e5065ef0b', 'docs/verification/20261125-p26/archive-v4/INPUT_PATHS.json': '417c7e0821fc9a44ed7a3f0a17307a452c84fe012619f4172defecc09cf7bf6d', 'docs/verification/20261125-p26/archive-v4/ORIGINAL_INPUT_SCALE.json': '3e022a419c35152589c2c3fb26cb0fe5839c79a348277b0643174b4f078f3954', 'docs/verification/20261125-p26/archive-v4/SEMANTIC_DIFF.json': 'ae7b47edccd42c15613d6a0281aedcba5656a3c52474c296c4d811abb6edfc35', 'docs/verification/20261125-p26/archive-v4/SOURCE_CLOSURE.json': 'bbc87a80e222cc24ddf46c87aaa5af04fef8c75f1c332979ec08f87caeaafcfb', 'docs/verification/20261125-p26/archive-v4/ACCEPTANCE_PLAN.json': 'dcb08837ef188aedeb1af3876925b35aa3891ee118c9978c10fd10f0ef84539d'}
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOL_SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
CONFIG_OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'
CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
EVIDENCE_PINS = {
    CONFIG_OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614',
    CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880',
}
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
    return {'commit': source_commit, 'path': PREFIX + path if module in OWNERS else path}


def validate_manifest(manifest, module, h):
    need(manifest.get('schema') == 'p26_archive_v4_strict_input_targets_v1' and
         manifest.get('owner_count') == 32 and manifest.get('owners') == OWNER_ORDER and
         set(manifest.get('modules', {})) == OWNERS and module in OWNERS and
         manifest.get('excluded_closed_guard_facade') == FACADE and
         manifest.get('excluded_existing_reader_target') == READER and
         manifest.get('frozen_existing_module_count') == 218 and
         manifest.get('review_input_pins') == REVIEW_INPUT_PINS and
         manifest.get('old_core_224_exports_credit_transferred') is False and
         manifest.get('archive_complete') is False,
         'Archive v4 input scope or reviewed manifest differs')
    catalog = manifest.get('all_project_source_catalog', {})
    need(isinstance(catalog, dict) and len(catalog) == 250 and
         FACADE not in catalog and READER in catalog and OWNERS <= set(catalog),
         'Archive v4 frozen source catalog differs')
    for m, row in catalog.items():
        need(row.get('path') == h.module_path(m) and
             row.get('source_path') == source_origin('unused', m, h)['path'] and
             re.fullmatch(r'[0-9a-f]{64}', row.get('sha256', '')) is not None and
             type(row.get('bytes')) is int and row['bytes'] > 0 and
             isinstance(row.get('imports'), list) and all(isinstance(x, str) for x in row['imports']),
             'Frozen project source record differs: ' + m)
    graph = {m: [d for d in r['imports'] if d.startswith('ImbalancedChen.')]
             for m, r in catalog.items()}
    for m, row in manifest['modules'].items():
        need(all(row.get(k) == catalog[m][k] for k in catalog[m]) and
             row.get('known_preimages') == ([CORE_PREIMAGE] if m == CORE else []) and
             row.get('project_closure_count') == len(h.closure(graph, [m])) and
             isinstance(row.get('required_accepted_owners'), list) and
             len(row['required_accepted_owners']) == len(set(row['required_accepted_owners'])) and
             all(x in OWNERS and OWNER_ORDER.index(x) < OWNER_ORDER.index(m)
                 for x in row['required_accepted_owners']) and
             ((h.closure(graph, [m]) & OWNERS) - {m}) <= set(row['required_accepted_owners']),
             'Owner preimage, closure or preceding strict acceptance differs: ' + m)


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


def production_archive_snapshot(project, d, manifest):
    path = project / 'ImbalancedChen/P2OriginalSaving19Archive.lean'
    need(path.is_file() and not path.is_symlink(), 'production Archive is not a regular source file')
    record = {'path': str(path), **d.fingerprint(path)}
    need(record['sha256'] in manifest['production_archive_allowed_sha256'],
         'production Archive is not an explicitly reviewed preimage/target; this runner never changes it')
    return record


def loader_input_snapshot(project, d, expected):
    records, differences = [], []
    for family, stem, suffix in (
        ('geometry', 'eighth-third-minorant-extension-20261009-a23-s23_low-', '-cell.witness.json'),
        ('moment', 'eighth-third-moment-refinement-20261009-a23-low-', '.witness.json')):
        for cell in range(13):
            relative = '../goldbach-research/' + stem + f'{cell:02d}' + suffix
            path = project / relative
            logical = os.path.abspath(path)
            try:
                resolved = path.resolve(strict=True)
                need(path.is_file(), 'loader input is not a regular file')
                record = {'family': family, 'cell': cell, 'loader_relative_path': relative,
                          'loader_absolute_path': logical, 'resolved_actual_path': str(resolved),
                          **d.fingerprint(path)}
                need(path.resolve(strict=True) == resolved, 'loader input target changed while hashing')
                records.append(record)
            except (OSError, RuntimeError) as error:
                differences.append({'family': family, 'cell': cell, 'loader_relative_path': relative,
                                    'loader_absolute_path': logical, 'error': str(error)})
    need(not differences, 'ARCHIVE_LOADER_INPUTS_UNAVAILABLE ' + json.dumps(differences, sort_keys=True))
    need(len(records) == 26 and len({r['loader_absolute_path'] for r in records}) == 26,
         'Archive loader input scope differs')
    need(records == expected, 'ARCHIVE_ORIGINAL_BYTES_DIFFER_FROM_REVIEWED_26_INPUTS')
    return records


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
    need(sha(raw[MANIFEST]) == MANIFEST_SHA, 'Archive v4 strict target manifest pin differs')
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
         FACADE not in graph, 'selected owner missing, wrong closure size, or closed-guard facade imported')
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
    production = production_archive_snapshot(args.project, d, manifest)
    loader_inputs = loader_input_snapshot(args.project, d, manifest['original_loader_inputs'])
    provenance = {
        'schema': 'p26_archive_v4_strict_single_input_owner_v1',
        'source_commit': args.source_commit, 'reviewed_p1_baseline': P1_BASE, 'module': args.module,
        'manifest_path': MANIFEST, 'manifest_sha256': sha(raw[MANIFEST]), 'manifest_owner_count': 32,
        'target_source_sha256': sources[args.module],
        'allowed_existing_target_sha256': sorted({sources[args.module]} |
                                                  set(manifest['modules'][args.module]['known_preimages'])),
        'all_project_sources_from_one_commit': True,
        'project_source_origins': {m: source_origin(args.source_commit, m, h) for m in sorted(sources)},
        'project_sources_after_single_target_install': sources,
        'source_closure_count': len(sources), 'project_import_graph': graph,
        'retained_dependencies_only_checked_for_readiness': sorted(selected - OWNERS),
        'required_preceding_strict_owners': required,
        'production_archive_source': production,
        'loader_inputs': loader_inputs,
        'loader_input_identity_scope': 'all_26_actual_files_at_unchanged_original_loader_paths',
        'old_core_224_exports_credit_transferred': False,
        'selected_input_owner_only': True, 'archive_complete': False,
        'only_cell00_proved': False, 'proved_parse_cells': [],
        'archive_shape_or_row_guards_proved': False,
        'whole_P1_complete': False, 'whole_P2_complete': False,
    }
    return types.SimpleNamespace(api=api, h=h, ops=ops, d=d, raw=raw, payload=payload,
                                 graph=graph, sources=sources, provenance=provenance,
                                 all_graph=all_graph, all_sources=all_sources, manifest=manifest,
                                 source_config=source_config, runtime_config=runtime_config, slot=slot,
                                 source_commit=args.source_commit, module=args.module)


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
                    'after_sha256': sha(spec.payload), 'cloud_source_mutation_required': m == CORE}]
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
    need(production_archive_snapshot(PROJECT, spec.d, spec.manifest) ==
         spec.provenance['production_archive_source'],
         'unselected production Archive source changed during input acceptance')


def require_accepted_owners(spec, frozen, run):
    """Read-validate prior normal/full-owned receipts; never compile or audit dependencies."""
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
             prior['loader_inputs'] == frozen['loader_inputs'] and
             prior['production_archive_source'] == frozen['production_archive_source'] and
             all(prior[k] == frozen[k] for k in ('project', 'runtime', 'runtime_configuration',
                                               'source_configuration', 'configuration_basis',
                                               'manifest_path', 'manifest_sha256', 'manifest_owner_count',
                                               'api_commit', 'tooling_commit', 'driver_sha256')),
             'preceding owner requires this exact source closure, loader input and strict runtime: ' + module)
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
                            api.read_json(directory / 'AUDIT_PLAN.json'), {module: normal},
                            graph, sources, h, d))
            result = directory / 'lane-0/VALIDATION_RESULTS.json'
            audits.append({'path': str(result), **d.fingerprint(result)})
        need(accepted == {module}, 'preceding owner lacks full strict acceptance: ' + module)
        successful = []
        for result_path in sorted((root / 'runs').glob('attempt-*/RESULT.json')):
            result = api.read_json(result_path)
            if result.get('status') != api.PASS or result.get('error') is not None:
                continue
            directory = result_path.parent
            need(result['module'] == module and result['source_commit'] == spec.source_commit and
                 result['accepted_owners'] == [module] and result['all_selected_owners_accepted'] is True and
                 result['archive_complete'] is False and result['only_cell00_proved'] is False and
                 result['project_source_origins'] == origins and
                 result['project_sources_after_single_target_install'] == sources and
                 result['loader_inputs'] == frozen['loader_inputs'],
                 'preceding owner wrapper completion differs: ' + module)
            evidence = [result_path]
            for name in ('LOADER_INPUTS_BEFORE.json', 'LOADER_INPUTS_AFTER.json'):
                path = directory / name
                need(api.read_json(path) == frozen['loader_inputs'], 'preceding raw input snapshot differs')
                evidence.append(path)
            for name in ('P1_DEPENDENCY_CONTEXT_BEFORE.json', 'P1_DEPENDENCY_CONTEXT_AFTER.json'):
                path = directory / name
                need(api.read_json(path)['context'] == current, 'preceding source/object context differs')
                evidence.append(path)
            successful.append([{'path': str(p), **d.fingerprint(p)} for p in evidence])
        need(successful, 'preceding owner has no successful wrapper run with unchanged raw inputs: ' + module)
        summaries.append({'module': module, 'recompiled': False, 'reaudited': False,
                          'normal_receipt': {'path': str(normal_path), **d.fingerprint(normal_path)},
                          'audit_receipts': audits, 'successful_wrapper_runs': successful})
    d.save(run / 'REUSED_PRECEDING_ACCEPTANCE.json', summaries)


def worker(spec, root, run):
    api, h, ops, d, m = spec.api, spec.h, spec.ops, spec.d, spec.module
    d.verify_lane(h)
    frozen = api.read_json(root / 'BINDING.json')
    need(frozen == binding(spec), 'serialized worker binding changed')
    passed, accepted, error, before = {}, set(), None, None
    try:
        loader_before = loader_input_snapshot(PROJECT, d, spec.manifest['original_loader_inputs'])
        d.save(run / 'LOADER_INPUTS_BEFORE.json', loader_before)
        need(loader_before == frozen['loader_inputs'], 'actual loader inputs changed before acceptance')
        require_accepted_owners(spec, frozen, run)
        install_one(spec, run)
        check_installed(spec, frozen['runtime'])
        before = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_BEFORE.json', {'provenance': spec.provenance, 'context': before})
        passed[m] = api.normal_one(spec.source_commit, PROJECT, root, m, spec.graph, spec.sources, h, ops, d)
        api.audit(spec.source_commit, PROJECT, root, passed, spec.graph, spec.sources, h, ops, d, run, accepted)
    except Exception as caught:
        error = str(caught)
        ops.emit('P26_ARCHIVE_V4_INPUT_HELD_OR_FAILED', module=m, reason=error)
    try:
        check_installed(spec, frozen['runtime'])
        after = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_AFTER.json', {'provenance': spec.provenance, 'context': after})
        need(before is not None and after == before,
             'source/object/trace/configuration/runtime context changed during acceptance')
    except Exception as caught:
        context_error = str(caught)
        d.save(run / 'CONTEXT_AFTER_ERROR.json', {'error': context_error})
        error = context_error if error is None else error + '; POST_CONTEXT: ' + context_error
    try:
        loader_after = loader_input_snapshot(PROJECT, d, spec.manifest['original_loader_inputs'])
        d.save(run / 'LOADER_INPUTS_AFTER.json', loader_after)
        need(loader_after == frozen['loader_inputs'], 'actual loader inputs changed during acceptance')
    except Exception as caught:
        loader_error = str(caught)
        d.save(run / 'LOADER_INPUTS_AFTER_ERROR.json', {'error': loader_error})
        error = loader_error if error is None else error + '; POST_LOADER_INPUTS: ' + loader_error
    complete = accepted == {m} and error is None
    result = {**spec.provenance, 'status': api.PASS if complete else 'HELD_OR_FAILED',
              'normal_passed': sorted(passed), 'accepted_owners': sorted(accepted), 'error': error,
              'accepted_for_actual_P1_context_only': complete, 'all_selected_owners_accepted': complete,
              'archive_complete': False, 'only_cell00_proved': False,
              'proved_parse_cells': [], 'archive_shape_or_row_guards_proved': False}
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
