#!/usr/bin/env python3
"""Accept only v3 Parse00 over the exact already accepted v2 Core context.

The selected Parse00 source comes from --source-commit. Its 219 project
dependencies retain their explicit 508d7579 commit/path origins. The pinned
v2 wrapper supplies its unchanged source/configuration/fixture checks and its
Core receipt validator; Batch13 supplies unchanged normal/kernel/full-owned
acceptance. Core normal or audit commands are never rerun or relabelled.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-p26-archive-diagnostic-v3')
CORE_ACCEPTED_COMMIT = '508d757913ea9c536c0d4f95abb35c090b940a29'
CORE = 'ImbalancedChen.P2OriginalSaving19ArchiveCore'
MODULE = 'ImbalancedChen.P2OriginalSaving19ArchiveParse00'
V2_PREFIX = 'docs/verification/20261125-p26/archive-v2/'
V3_PREFIX = 'docs/verification/20261125-p26/archive-v3/'
CORE_DRIVER_PATH = 'docs/verification/20261125-p26/verify/run_archive_diagnostic_v2.py'
CORE_DRIVER_SHA = 'fdfcb29fd4c2a40c5b9566979b96df2abd322634a9676b8556f8034941a35a56'
CORE_MANIFEST = V2_PREFIX + 'SOURCE_MANIFEST.json'
CORE_MANIFEST_SHA = 'c1bc944d95142056df504715617cd0d5c008c27d3cd5d25ee1b87a1961602e7d'
CORE_ROOT = (Path('/workspace/p1-complete-proof/20261125-p26-archive-diagnostic-v2') /
             CORE_ACCEPTED_COMMIT / CORE)
CORE_SHA = 'df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182'
OLD_PARSE_SHA = '8550c64fea8f8716042df6509d9cdb29b93a77eb3fd74ca212398b9ce3cb430d'
TARGET_PATH = V3_PREFIX + MODULE.replace('.', '/') + '.lean'
TARGET_SHA = '4560166cebd3de5fc7ec28b148e024589993ebdd7ea0e6b2bf11f935f3950979'
MANIFEST = V3_PREFIX + 'SOURCE_MANIFEST.json'
MANIFEST_SHA = 'e5912c4fbc63d861d98dc0a5fbe9a1800c4e6774ef3b92b14943a0e4a48eaf53'
PRODUCTION_ARCHIVE_SHA = 'f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)


def source_inputs(args):
    need(args.module == MODULE and re.fullmatch(r'[0-9a-f]{40}', args.source_commit) is not None and
         args.source_commit != CORE_ACCEPTED_COMMIT,
         'v3 selects only Parse00 from an explicit new full commit SHA')
    need(subprocess.check_output(['git', 'cat-file', '-t', args.source_commit],
                                 cwd=args.source_repo).strip() == b'commit', 'new Parse00 commit unavailable')
    need(subprocess.run(['git', 'merge-base', '--is-ancestor', CORE_ACCEPTED_COMMIT, args.source_commit],
                        cwd=args.source_repo, check=False).returncode == 0,
         'new Parse00 source commit must descend from the accepted Core source commit')
    old_driver = git(args.source_repo, CORE_ACCEPTED_COMMIT, CORE_DRIVER_PATH)
    need(sha(old_driver) == CORE_DRIVER_SHA, 'accepted v2 wrapper source pin differs')
    v2 = types.ModuleType('pinned_accepted_archive_v2_wrapper')
    v2.__file__ = '<pinned Git object: ' + CORE_DRIVER_PATH + '>'
    exec(compile(old_driver, v2.__file__, 'exec'), v2.__dict__)
    need(v2.PROJECT == PROJECT and v2.REPO == REPO and v2.CORE == CORE and v2.PARSE00 == MODULE and
         v2.MANIFEST == CORE_MANIFEST and v2.MANIFEST_SHA == CORE_MANIFEST_SHA and
         v2.PRODUCTION_ARCHIVE_SHA == PRODUCTION_ARCHIVE_SHA and
         v2.ROOT / CORE_ACCEPTED_COMMIT / CORE == CORE_ROOT,
         'accepted v2 wrapper identity or frozen environment differs')
    core_args = types.SimpleNamespace(source_commit=CORE_ACCEPTED_COMMIT, module=CORE,
                                     source_repo=args.source_repo, project=args.project,
                                     config_basis=args.config_basis)
    core_spec = v2.source_inputs(core_args)
    api, h, ops, d = core_spec.api, core_spec.h, core_spec.ops, core_spec.d
    need(len(core_spec.sources) == 219 and core_spec.sources[CORE] == CORE_SHA and
         MODULE not in core_spec.sources and core_spec.slot['exists'] and
         core_spec.slot['sha256'] == CORE_SHA,
         'v3 requires all 219 accepted dependencies, including the already installed exact Core')
    raw = dict(core_spec.raw)
    raw[CORE_DRIVER_PATH] = old_driver
    raw[MANIFEST] = git(args.source_repo, args.source_commit, MANIFEST)
    payload = git(args.source_repo, args.source_commit, TARGET_PATH)
    raw[TARGET_PATH] = payload
    need(sha(raw[MANIFEST]) == MANIFEST_SHA and sha(payload) == TARGET_SHA and len(payload) == 1568,
         'reviewed v3 Parse00 source or manifest differs')
    manifest = json.loads(raw[MANIFEST])
    need(manifest['candidate_source_repository_path'] == TARGET_PATH and
         manifest['candidate_install_path'] == h.module_path(MODULE) and
         manifest['candidate_sha256'] == TARGET_SHA and manifest['baseline_sha256'] == OLD_PARSE_SHA and
         manifest['core_reuse']['accepted_source_commit'] == CORE_ACCEPTED_COMMIT and
         manifest['core_reuse']['driver_sha256'] == CORE_DRIVER_SHA and
         manifest['core_reuse']['manifest_sha256'] == CORE_MANIFEST_SHA and
         manifest['production_archive_sha256'] == PRODUCTION_ARCHIVE_SHA,
         'v3 target or accepted-Core origin manifest differs')
    original_parse = core_spec.raw[V2_PREFIX + h.module_path(MODULE)]
    public_statements = lambda data: re.findall(r'^theorem\s+(\w+)\s*:\s*(.*?)\s*:=',
                                               data.decode(), re.M | re.S)
    need(sha(original_parse) == OLD_PARSE_SHA and
         public_statements(original_parse) == public_statements(payload) and
         len(public_statements(payload)) == 2 and h.imports(payload) == [CORE],
         'v3 must preserve the exact two original public statements and the Core-only import')
    graph = {**core_spec.graph, MODULE: [CORE]}
    sources = {**core_spec.sources, MODULE: TARGET_SHA}
    need(h.closure(graph, [MODULE]) == set(sources) and len(sources) == 220,
         'v3 mixed-source closure differs')
    slot = v2.source_slot(args.project, MODULE, payload, h)
    origins = {**core_spec.provenance['project_source_origins'],
               MODULE: {'commit': args.source_commit, 'path': TARGET_PATH}}
    need(all(origins[m]['commit'] == CORE_ACCEPTED_COMMIT for m in sources if m != MODULE),
         'dependency origin was relabelled as the new target commit')
    input_origins = {}
    for path in core_spec.raw:
        commit = (v2.API_COMMIT if path == v2.API_PATH else
                  v2.TOOL_SOURCE if path in api.PINS else
                  v2.P1_BASE if path in v2.EVIDENCE_PINS else CORE_ACCEPTED_COMMIT)
        input_origins[path] = {'commit': commit, 'path': path}
    input_origins.update({CORE_DRIVER_PATH: {'commit': CORE_ACCEPTED_COMMIT, 'path': CORE_DRIVER_PATH},
                          MANIFEST: {'commit': args.source_commit, 'path': MANIFEST},
                          TARGET_PATH: {'commit': args.source_commit, 'path': TARGET_PATH}})
    provenance = {
        'schema': 'p26_archive_parse00_target_over_accepted_v2_core_v3',
        'source_commit': args.source_commit, 'target_source_commit': args.source_commit,
        'dependency_source_commit': CORE_ACCEPTED_COMMIT, 'module': MODULE,
        'engine_source_commit_scope': 'selected_Parse00_owner_only_not_entire_project_tree',
        'manifest_path': MANIFEST, 'manifest_sha256': MANIFEST_SHA,
        'target_source_sha256': TARGET_SHA, 'allowed_existing_target_sha256': [TARGET_SHA],
        'known_failed_parse_preimage_sha256': OLD_PARSE_SHA,
        'known_preimage_replacements_performed_by_driver': False,
        'project_source_origins': origins, 'project_sources_after_single_target_install': sources,
        'project_import_graph': graph, 'source_closure_count': 220,
        'accepted_dependency_source_count': 219, 'input_source_origins': input_origins,
        'accepted_Core': {'source_commit': CORE_ACCEPTED_COMMIT, 'module': CORE,
                          'source_path': V2_PREFIX + h.module_path(CORE), 'source_sha256': CORE_SHA,
                          'driver_path': CORE_DRIVER_PATH, 'driver_sha256': CORE_DRIVER_SHA,
                          'manifest_path': CORE_MANIFEST, 'manifest_sha256': CORE_MANIFEST_SHA,
                          'acceptance_root': str(CORE_ROOT), 'old_receipts_relabelled': False,
                          'normal_or_audit_repeated': False},
        'production_archive_source': core_spec.provenance['production_archive_source'],
        'diagnostic_only': True, 'archive_complete': False, 'parse_cells_requested': [0],
        'fixture_mathematical_audit_performed': False, 'whole_P1_complete': False, 'whole_P2_complete': False,
    }
    return types.SimpleNamespace(v2=v2, core_spec=core_spec, api=api, h=h, ops=ops, d=d,
                                 raw=raw, payload=payload, graph=graph, sources=sources, slot=slot,
                                 provenance=provenance, source_commit=args.source_commit, module=MODULE,
                                 source_config=core_spec.source_config, runtime_config=core_spec.runtime_config)


def inputs(args):
    spec = source_inputs(args)
    snapshot = spec.v2.loader_input_snapshot(args.project, spec.d)
    for item in (spec, spec.core_spec):
        item.loader_inputs = snapshot
        item.provenance['loader_inputs'] = snapshot
        item.provenance['loader_input_identity_scope'] = 'actual_files_at_unchanged_original_loader_paths'
    return spec


def expected_core_binding(spec):
    old, v2 = spec.core_spec, spec.v2
    return {**old.provenance, 'project': str(PROJECT), 'api_commit': v2.API_COMMIT,
            'tooling_commit': v2.TOOL_SOURCE, 'input_sha256': {p: sha(b) for p, b in old.raw.items()},
            'driver_sha256': CORE_DRIVER_SHA, 'configuration_basis': 'runtime',
            'source_configuration': old.source_config, 'runtime_configuration': old.runtime_config,
            'runtime': old.d.runtime_binding(old.h)}


def binding(spec):
    return {**spec.provenance, 'project': str(PROJECT), 'api_commit': spec.v2.API_COMMIT,
            'tooling_commit': spec.v2.TOOL_SOURCE, 'input_sha256': {p: sha(b) for p, b in spec.raw.items()},
            'driver_sha256': sha(Path(__file__).read_bytes()), 'configuration_basis': 'runtime',
            'source_configuration': spec.source_config, 'runtime_configuration': spec.runtime_config,
            'runtime': spec.d.runtime_binding(spec.h)}


def require_accepted_core(spec, run):
    old_binding = spec.api.read_json(CORE_ROOT / 'BINDING.json')
    expected = expected_core_binding(spec)
    need(old_binding == expected, 'accepted Core full binding differs from its actual old-commit context')
    need(spec.d.fingerprint(CORE_ROOT / 'executed-driver.py')['sha256'] == CORE_DRIVER_SHA,
         'accepted Core frozen v2 driver changed')
    # Use the unchanged v2 Parse00 precondition validator with ONLY the old Core
    # source context. It calls normal_valid/audit_valid with 508d, never normal_one/audit.
    old_context = types.SimpleNamespace(**vars(spec.core_spec))
    old_context.module = MODULE
    need(old_context.source_commit == CORE_ACCEPTED_COMMIT and len(old_context.sources) == 219,
         'accepted Core validator must retain its original source commit and source scope')
    spec.v2.require_accepted_core(old_context, expected, run)
    spec.d.save(run / 'REUSED_CORE_IDENTITY.json', {
        'source_commit': CORE_ACCEPTED_COMMIT, 'binding_path': str(CORE_ROOT / 'BINDING.json'),
        'binding_file': spec.d.fingerprint(CORE_ROOT / 'BINDING.json'),
        'driver_sha256': CORE_DRIVER_SHA, 'manifest_sha256': CORE_MANIFEST_SHA,
        'normal_valid_source_commit': CORE_ACCEPTED_COMMIT, 'audit_valid_source_commit': CORE_ACCEPTED_COMMIT,
        'normal_or_audit_commands_repeated': False, 'old_receipts_relabelled': False})


def worker(spec, root, run):
    api, h, ops, d = spec.api, spec.h, spec.ops, spec.d
    d.verify_lane(h)
    frozen = api.read_json(root / 'BINDING.json')
    need(frozen == binding(spec), 'serialized v3 worker binding changed')
    passed, accepted, before, error = {}, set(), None, None
    try:
        loader_before = spec.v2.loader_input_snapshot(PROJECT, d)
        d.save(run / 'LOADER_INPUTS_BEFORE.json', loader_before)
        need(loader_before == frozen['loader_inputs'], 'actual loader inputs changed before v3 acceptance')
        require_accepted_core(spec, run)
        spec.v2.install_one(spec, run)
        spec.v2.check_installed(spec, frozen['runtime'])
        before = api.context(spec.source_commit, PROJECT, MODULE, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_BEFORE.json', {'provenance': spec.provenance, 'context': before})
        passed[MODULE] = api.normal_one(spec.source_commit, PROJECT, root, MODULE,
                                        spec.graph, spec.sources, h, ops, d)
        api.audit(spec.source_commit, PROJECT, root, passed, spec.graph, spec.sources, h, ops, d, run, accepted)
    except Exception as caught:
        error = str(caught)
        ops.emit('P26_ARCHIVE_V3_PARSE00_HELD_OR_FAILED', module=MODULE, reason=error)
    try:
        spec.v2.check_installed(spec, frozen['runtime'])
        after = api.context(spec.source_commit, PROJECT, MODULE, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_AFTER.json', {'provenance': spec.provenance, 'context': after})
        need(before is not None and after == before, 'source/object/trace/configuration/runtime context changed')
    except Exception as caught:
        detail = str(caught)
        d.save(run / 'CONTEXT_AFTER_ERROR.json', {'error': detail})
        error = detail if error is None else error + '; POST_CONTEXT: ' + detail
    try:
        loader_after = spec.v2.loader_input_snapshot(PROJECT, d)
        d.save(run / 'LOADER_INPUTS_AFTER.json', loader_after)
        need(loader_after == frozen['loader_inputs'], 'actual loader inputs changed during v3 acceptance')
    except Exception as caught:
        detail = str(caught)
        d.save(run / 'LOADER_INPUTS_AFTER_ERROR.json', {'error': detail})
        error = detail if error is None else error + '; POST_LOADER_INPUTS: ' + detail
    complete = accepted == {MODULE} and error is None
    result = {**spec.provenance, 'status': api.PASS if complete else 'HELD_OR_FAILED',
              'normal_passed': sorted(passed), 'accepted_owners': sorted(accepted), 'error': error,
              'all_selected_owners_accepted': complete, 'accepted_for_actual_P1_context_only': complete,
              'archive_complete': False, 'only_cell00_proved': complete,
              'proved_parse_cells': [0] if complete else [], 'archive_shape_or_row_guards_proved': False}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0 if complete else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--module', choices=(MODULE,), default=MODULE)
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
        need(args.source_repo == REPO and args.project == PROJECT, 'execution is restricted to the existing P1 project')
    spec = inputs(args)
    api, h, ops, d = spec.api, spec.h, spec.ops, spec.d
    root = ROOT / args.source_commit / MODULE
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        print(json.dumps({**spec.provenance, 'target_installation_preflight': spec.slot,
              'status': 'SOURCE_CONFIG_ONLY_NOT_CLOUD_READY' if args.config_basis == 'source' else
                        'READ_ONLY_SOURCE_RUNTIME_CHECK_PASS_NOT_ACCEPTANCE',
              'accepted_Core_receipts_not_checked_by_check_mode': True,
              'source_installation_performed': False, 'cloud_compilation_performed': False,
              'only_cell00_proved': False}, sort_keys=True))
        return 0
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid run directory')
        return worker(spec, root, run)
    need(args.run_dir is None, 'run-dir requires serialized worker')
    original = d.original_git_state(REPO)
    d.save(root / 'BINDING.json', binding(spec))
    for path, data in spec.raw.items():
        # Preserve both v2/v3 manifest and Parse00 basenames without collisions.
        destination = root / 'inputs' / ('e9.py' if path == api.E9 else 'git/' + path)
        d.write_frozen(destination, data)
    executed = root / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--source-commit', args.source_commit,
             '--module', MODULE, '--run', '--inside-lane', '--run-dir', str(run)]
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(REPO)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty Git source worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
