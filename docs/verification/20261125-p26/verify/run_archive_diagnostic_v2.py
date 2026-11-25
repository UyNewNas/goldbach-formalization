#!/usr/bin/env python3
"""Diagnose one of two original-representation Archive owners in the P1 lane.

The repaired diagnostic source comes from the reviewed v2 docs path; production
imports come from one descendant of the original aa8e91cd source commit.
Only Root installs the known-preimage production and failed-Core replacements. Only the selected absent/identical owner is
installed. All 26 actual loader inputs are frozen before/after; Parse00 reuses
Core only with the same inputs and validated original normal/audit receipts.
The published Batch13 acceptance engine and existing runtime remain unchanged.
No fixture mathematics is audited here. Complete Archive acceptance is false.
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
ROOT = Path('/workspace/p1-complete-proof/20261125-p26-archive-diagnostic-v2')
BASE_COMMIT = 'aa8e91cd99e6b3f6c61417271ab105d3077d010d'
P1_BASE = '298670f119d24874b719facb3ef756f1e01223a1'
PREFIX = 'docs/verification/20261125-p26/archive-v2/'
V1_PREFIX = 'docs/verification/20261125-p26/archive/'
MANIFEST = PREFIX + 'SOURCE_MANIFEST.json'
MANIFEST_SHA = 'c1bc944d95142056df504715617cd0d5c008c27d3cd5d25ee1b87a1961602e7d'
CORE = 'ImbalancedChen.P2OriginalSaving19ArchiveCore'
PARSE00 = 'ImbalancedChen.P2OriginalSaving19ArchiveParse00'
OWNERS = {CORE, PARSE00}
OWNER_PINS = {
    CORE: {'bytes': 8552, 'sha256': 'df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182'},
    PARSE00: {'bytes': 878, 'sha256': '8550c64fea8f8716042df6509d9cdb29b93a77eb3fd74ca212398b9ce3cb430d'},
}
PRODUCTION_ARCHIVE = 'ImbalancedChen/P2OriginalSaving19Archive.lean'
PRODUCTION_ARCHIVE_SHA = 'f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49'
PRODUCTION_PREIMAGE_SHA = 'b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6'
CORE_PREIMAGE_SHA = 'b784118a845f0470a231ce349ddead8f3a6f0d9f6aa297f10079acbffdda9960'
OLD_LOADER = 'let s ← liftIO <| IO.FS.readFile p'.encode()
NEW_LOADER = 'let s ← IO.FS.readFile p'.encode()
PREFIX_BYTES = 8151
PREFIX_SHA = '714943068685d3a2fb3bf59ed8c027b5165ab777517733934231d0451f6862d6'
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


def validate_manifest(manifest, raw, repo, h, source_commit):
    need(sha(raw[MANIFEST]) == MANIFEST_SHA and
         manifest.get('schema') == 'p26_saving19_archive_loader_monadlift_repair_v2' and
         manifest.get('base_commit') == BASE_COMMIT and
         manifest.get('source_repository_path') == PRODUCTION_ARCHIVE and
         manifest.get('source_sha256') == PRODUCTION_ARCHIVE_SHA and
         manifest.get('original_source_sha256') == PRODUCTION_PREIMAGE_SHA and
         manifest.get('slice_start_byte') == 0 and
         manifest.get('slice_end_byte_exclusive') == PREFIX_BYTES and
         manifest.get('original_slice_end_byte_exclusive') == 8171 and
         manifest.get('slice_sha256') == PREFIX_SHA,
         'reviewed v2 Archive diagnostic manifest or exact prefix differs')
    rows = {row['module']: {k: row[k] for k in ('path', 'install_path', 'bytes', 'sha256')}
            for row in manifest.get('candidate_files', [])}
    expected = {m: {'path': source_origin(source_commit, m, h)['path'],
                    'install_path': h.module_path(m), **pin} for m, pin in OWNER_PINS.items()}
    need(len(manifest.get('candidate_files', [])) == 2 and rows == expected,
         'v2 Archive manifest must name exactly the two pinned diagnostic source origins')
    production_before = git(repo, BASE_COMMIT, PRODUCTION_ARCHIVE)
    production = git(repo, source_commit, PRODUCTION_ARCHIVE)
    need(sha(production_before) == PRODUCTION_PREIMAGE_SHA and
         sha(production) == PRODUCTION_ARCHIVE_SHA and len(production) == manifest['source_bytes'] == 10816 and
         production_before.count(OLD_LOADER) == 2 and production.count(NEW_LOADER) == 2 and
         production == production_before.replace(OLD_LOADER, NEW_LOADER) and
         len(production_before) - len(production) == 20,
         'production Archive must contain exactly the two reviewed loader repairs')
    for m, pin in OWNER_PINS.items():
        origin = source_origin(source_commit, m, h)
        data = git(repo, origin['commit'], origin['path'])
        need({'bytes': len(data), 'sha256': sha(data)} == pin, 'reviewed v2 diagnostic source differs: ' + m)
        raw[origin['path']] = data
    core = raw[source_origin(source_commit, CORE, h)['path']]
    core_before = git(repo, BASE_COMMIT, V1_PREFIX + h.module_path(CORE))
    need(sha(core_before) == CORE_PREIMAGE_SHA and core_before.count(OLD_LOADER) == 2 and
         core == core_before.replace(OLD_LOADER, NEW_LOADER) and
         core[:PREFIX_BYTES] == production[:PREFIX_BYTES] and sha(core[:PREFIX_BYTES]) == PREFIX_SHA,
         'Core is no longer the exact repaired production prefix with the original diagnostic suffix')


def loader_input_snapshot(project, d):
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
    return records


def production_archive_snapshot(project, d):
    path = project / PRODUCTION_ARCHIVE
    need(path.is_file() and not path.is_symlink(), 'production Archive is not a regular source file')
    fingerprint = d.fingerprint(path)
    need(fingerprint['sha256'] == PRODUCTION_ARCHIVE_SHA,
         'Root must install the reviewed production loader repair first; this driver cannot replace it')
    return {'path': str(path), **fingerprint}


def source_slot(project, module, payload, h):
    path = project / h.module_path(module)
    need(path.parent.is_dir() and not path.parent.is_symlink() and not path.is_symlink(),
         'target or target directory is a symlink or missing directory: ' + str(path))
    if not os.path.lexists(path):
        return {'exists': False, 'sha256': None, 'bytes': None, 'action': 'CREATE_NEW_ABSENT'}
    need(path.is_file(), 'target is not a regular file: ' + str(path))
    data = path.read_bytes()
    digest = sha(data)
    allowed = {sha(payload)}
    need(digest in allowed, 'UNKNOWN_SOURCE_PREIMAGE ' + json.dumps(
        {'module': module, 'actual_sha256': digest, 'allowed_sha256': sorted(allowed)}, sort_keys=True))
    return {'exists': True, 'sha256': digest, 'bytes': len(data),
            'action': 'ALREADY_AFTER_NOOP'}


def source_inputs(args):
    need(re.fullmatch(r'[0-9a-f]{40}', args.source_commit) is not None and
         args.source_commit != BASE_COMMIT and args.module in OWNERS,
         'v2 requires an explicit reviewed descendant commit and one of the two owners')
    need(subprocess.check_output(['git', 'cat-file', '-t', args.source_commit],
                                 cwd=args.source_repo).strip() == b'commit', 'source commit unavailable')
    need(subprocess.run(['git', 'merge-base', '--is-ancestor', BASE_COMMIT, args.source_commit],
                        cwd=args.source_repo, check=False).returncode == 0,
         'v2 source commit must descend from the original aa8e91cd P1 source closure')
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
    raw[MANIFEST] = git(args.source_repo, args.source_commit, MANIFEST)
    manifest = json.loads(raw[MANIFEST])
    validate_manifest(manifest, raw, args.source_repo, h, args.source_commit)
    graph, sources, pending, payload = {}, {}, [args.module], None
    while pending:
        m = pending.pop()
        if m in graph:
            continue
        origin = source_origin(args.source_commit, m, h)
        data = git(args.source_repo, origin['commit'], origin['path'])
        imports = h.imports(data)
        if m in OWNERS:
            need({'sha256': sha(data), 'bytes': len(data)} == OWNER_PINS[m],
                 'published diagnostic owner differs: ' + m)
        sources[m] = sha(data)
        graph[m] = [x for x in imports if x.startswith('ImbalancedChen.')]
        pending.extend(graph[m])
        if m == args.module:
            payload = data
            raw[origin['path']] = data
    need(payload is not None, 'selected owner payload missing')
    h.closure(graph, [args.module])
    need('ImbalancedChen.P2OriginalSaving19Archive' not in graph,
         'diagnostic Core and production Archive cannot share a Lean import environment')
    slot = source_slot(args.project, args.module, payload, h)
    differences = []
    for m in sorted(set(graph) - {args.module}):
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
    production = production_archive_snapshot(args.project, d)
    provenance = {
        'schema': 'p26_archive_diagnostic_single_owner_v2',
        'source_commit': args.source_commit, 'reviewed_p1_baseline': P1_BASE, 'module': args.module,
        'repair_base_commit': BASE_COMMIT, 'production_source_preimage_sha256': PRODUCTION_PREIMAGE_SHA,
        'failed_core_source_preimage_sha256': CORE_PREIMAGE_SHA,
        'known_preimage_replacements_performed_by_driver': False,
        'exact_repaired_prefix_bytes': PREFIX_BYTES, 'exact_repaired_prefix_sha256': PREFIX_SHA,
        'manifest_path': MANIFEST, 'manifest_sha256': sha(raw[MANIFEST]), 'manifest_owner_count': 2,
        'target_source_sha256': sources[args.module], 'allowed_existing_target_sha256': [sources[args.module]],
        'all_project_sources_from_one_commit': True,
        'project_source_origins': {m: source_origin(args.source_commit, m, h) for m in sorted(sources)},
        'project_sources_after_single_target_install': sources,
        'source_closure_count': len(sources), 'project_import_graph': graph,
        'diagnostic_only': True, 'archive_complete': False,
        'parse_cells_requested': [0] if args.module == PARSE00 else [],
        'core_contains_parse_success_proofs': False,
        'fixture_mathematical_audit_performed': False,
        'production_archive_source': production,
        'whole_P1_complete': False, 'whole_P2_complete': False,
    }
    return types.SimpleNamespace(api=api, h=h, ops=ops, d=d, raw=raw, payload=payload,
                                 graph=graph, sources=sources, provenance=provenance,
                                 source_config=source_config, runtime_config=runtime_config, slot=slot,
                                 source_commit=args.source_commit, module=args.module)


def inputs(args):
    spec = source_inputs(args)
    spec.loader_inputs = loader_input_snapshot(args.project, spec.d)
    spec.provenance['loader_inputs'] = spec.loader_inputs
    spec.provenance['loader_input_identity_scope'] = 'actual_files_at_unchanged_original_loader_paths'
    return spec


def binding(spec):
    return {**spec.provenance, 'project': str(PROJECT), 'api_commit': API_COMMIT,
            'tooling_commit': TOOL_SOURCE, 'input_sha256': {p: sha(b) for p, b in spec.raw.items()},
            'driver_sha256': sha(Path(__file__).read_bytes()), 'configuration_basis': 'runtime',
            'source_configuration': spec.source_config, 'runtime_configuration': spec.runtime_config,
            'runtime': spec.d.runtime_binding(spec.h)}


def install_one(spec, run):
    h, d, m = spec.h, spec.d, spec.module
    slot = source_slot(PROJECT, m, spec.payload, h)
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
    need(production_archive_snapshot(PROJECT, spec.d) == spec.provenance['production_archive_source'],
         'production Archive source changed during diagnostic acceptance')


def require_accepted_core(spec, frozen, run):
    """Read and validate existing Core evidence; never build or re-audit Core."""
    if spec.module != PARSE00:
        return
    api, h, d = spec.api, spec.h, spec.d
    root = ROOT / spec.source_commit / CORE
    core_binding = api.read_json(root / 'BINDING.json')
    owners = h.closure(spec.graph, [CORE])
    expected_sources = {m: spec.sources[m] for m in owners}
    need(core_binding['source_commit'] == spec.source_commit and core_binding['module'] == CORE and
         core_binding['loader_inputs'] == frozen['loader_inputs'] and
         core_binding['project_sources_after_single_target_install'] == expected_sources and
         core_binding['project_source_origins'] == {m: source_origin(spec.source_commit, m, h) for m in owners} and
         all(core_binding[k] == frozen[k] for k in ('runtime', 'runtime_configuration',
                                                  'source_configuration', 'manifest_sha256',
                                                  'api_commit', 'tooling_commit', 'driver_sha256')),
         'Parse00 requires Core accepted against these exact source origins, loader inputs and tools')
    normal_path = root / 'normal' / CORE / 'NORMAL_PASS.json'
    normal = api.read_json(normal_path)
    api.normal_valid(spec.source_commit, PROJECT, CORE, normal,
                     api.context(spec.source_commit, PROJECT, CORE, spec.graph, spec.sources, h, d), h, d)
    accepted, audit_receipts = set(), []
    for directory in sorted((root / 'audits').glob('*')):
        need(directory.is_dir() and not directory.is_symlink() and
             (directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
             'Core partial audit requires inspection: ' + str(directory))
        accepted.update(api.audit_valid(spec.source_commit, PROJECT, directory,
                        api.read_json(directory / 'AUDIT_PLAN.json'), {CORE: normal},
                        spec.graph, spec.sources, h, d))
        result = directory / 'lane-0/VALIDATION_RESULTS.json'
        audit_receipts.append({'path': str(result), **d.fingerprint(result)})
    need(accepted == {CORE}, 'Parse00 requires the complete Core normal/kernel/full-owned acceptance')
    successful_runs = []
    current_context = api.context(spec.source_commit, PROJECT, CORE, spec.graph, spec.sources, h, d)
    for result_path in sorted((root / 'runs').glob('attempt-*/RESULT.json')):
        result = api.read_json(result_path)
        if result.get('status') != api.PASS or result.get('error') is not None:
            continue
        directory = result_path.parent
        need(result['module'] == CORE and result['source_commit'] == spec.source_commit and
             result['accepted_owners'] == [CORE] and result['all_selected_owners_accepted'] is True and
             result['archive_complete'] is False and result['only_cell00_proved'] is False and
             result['project_source_origins'] == core_binding['project_source_origins'] and
             result['loader_inputs'] == frozen['loader_inputs'],
             'Core wrapper completion identity differs')
        evidence_paths = [result_path]
        for name in ('LOADER_INPUTS_BEFORE.json', 'LOADER_INPUTS_AFTER.json'):
            path = directory / name
            need(api.read_json(path) == frozen['loader_inputs'], 'Core actual loader-input snapshot differs')
            evidence_paths.append(path)
        for name in ('P1_DEPENDENCY_CONTEXT_BEFORE.json', 'P1_DEPENDENCY_CONTEXT_AFTER.json'):
            path = directory / name
            need(api.read_json(path)['context'] == current_context, 'Core wrapper dependency context differs')
            evidence_paths.append(path)
        successful_runs.append([{'path': str(path), **d.fingerprint(path)} for path in evidence_paths])
    need(successful_runs, 'Core has no successful wrapper completion with unchanged actual loader inputs')
    d.save(run / 'REUSED_CORE_ACCEPTANCE.json', {
        'module': CORE, 'recompiled': False, 'reaudited': False,
        'normal_receipt': {'path': str(normal_path), **d.fingerprint(normal_path)},
        'audit_receipts': audit_receipts, 'same_loader_inputs': True,
        'successful_wrapper_runs': successful_runs})


def worker(spec, root, run):
    api, h, ops, d, m = spec.api, spec.h, spec.ops, spec.d, spec.module
    d.verify_lane(h)
    frozen = api.read_json(root / 'BINDING.json')
    need(frozen == binding(spec), 'serialized worker binding changed')
    passed, accepted, error, before = {}, set(), None, None
    # External elaborator reads are not Lake dependencies; bind them separately.
    try:
        loader_before = loader_input_snapshot(PROJECT, d)
        d.save(run / 'LOADER_INPUTS_BEFORE.json', loader_before)
        need(loader_before == frozen['loader_inputs'], 'actual loader inputs changed before acceptance')
        require_accepted_core(spec, frozen, run)
        install_one(spec, run)
        check_installed(spec, frozen['runtime'])
        before = api.context(spec.source_commit, PROJECT, m, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_BEFORE.json', {'provenance': spec.provenance, 'context': before})
        passed[m] = api.normal_one(spec.source_commit, PROJECT, root, m, spec.graph, spec.sources, h, ops, d)
        api.audit(spec.source_commit, PROJECT, root, passed, spec.graph, spec.sources, h, ops, d, run, accepted)
    except Exception as caught:
        error = str(caught)
        ops.emit('P26_ARCHIVE_DIAGNOSTIC_HELD_OR_FAILED', module=m, reason=error)
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
        loader_after = loader_input_snapshot(PROJECT, d)
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
              'archive_complete': False, 'only_cell00_proved': complete and m == PARSE00,
              'proved_parse_cells': [0] if complete and m == PARSE00 else [],
              'archive_shape_or_row_guards_proved': False}
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
              'only_cell00_proved': False, 'proved_parse_cells': [],
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
