#!/usr/bin/env python3
"""Bind the one original NPY input to the existing P1 acceptance APIs.

This file does not change run_stage.py, materialize_sources.py or a validator.
Its worker is a direct child of the original serializer. Only the published
consumer source and original binary may be created, never overwritten.
Normal reuse additionally requires this adapter's original pre/post data join.
Interrupted attempts and the original API's partial-audit guard are preserved.
Worker evidence is provisional; only the outer, Git-checked acceptance is final.
No raw binary, source text or historical private logs are printed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError('Original NPY acceptance requires Python assertions')
sys.dont_write_bytecode = True
sys.setrecursionlimit(10000)

REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
PREFIX = 'docs/p1/20261125/p14-continuation/'
SCRIPT = PREFIX + 'run_original_npy.py'
MANIFEST = PREFIX + 'ORIGINAL_NPY_INPUT_MANIFEST.json'
DRIVER = PREFIX + 'run_stage.py'
DRIVER_SHA = 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1'
MATERIALIZER = PREFIX + 'materialize_sources.py'
MATERIALIZER_SHA = 'a074fc285a156eaf886e5a149e9e6f9f01a87f36500379f6c233a52f17dc0659'
MODULE = 'ImbalancedChen.P1HistoricalFifthOriginalNpyKernel'
SOURCE_PATH = MODULE.replace('.', '/') + '.lean'
FIXTURE = {
    'repository_path': 'ImbalancedChen/provenance/original-fifth/cells.npy',
    'install_path': 'ImbalancedChen/provenance/original-fifth/cells.npy',
    'consuming_module': MODULE, 'include_path': 'provenance/original-fifth/cells.npy',
    'bytes': 23410768,
    'sha256': 'd6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7',
    'git_blob_sha1': 'f32074559249efea10262584df57e1403b66c21c',
    'origin_commit': 'c6d6d5eed2b4a4c5a288645864e781716c7e5771',
    'origin_path': 'docs/source-only/20261102-certificates-l/original_npy_kernel/provenance/original-fifth/cells.npy',
}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)


def validate_manifest(manifest):
    need(manifest['schema'] == 'p14_original_npy_single_consumer_v1' and
         manifest['stage'] == 'original-npy-kernel' and
         manifest['whole_P1_4_complete'] is False, 'wrong fixed NPY stage')
    need(len(manifest['modules']) == 1, 'exactly one consumer is permitted')
    row = manifest['modules'][0]
    need(row['module'] == MODULE and row['path'] == SOURCE_PATH and
         type(row['bytes']) is int and row['bytes'] > 0 and
         re.fullmatch(r'[0-9a-f]{64}', row['sha256']) and
         re.fullmatch(r'[0-9a-f]{40}', row['git_blob_sha1']), 'consumer source identity differs')
    need(manifest['data_inputs'] == [FIXTURE], 'the original single fixture is fixed')


def checked_path(path, root):
    path, root = Path(path), Path(root)
    need(path.is_absolute() and path.is_relative_to(root), 'path escapes the fixed root')
    need(all(not p.is_symlink() for p in [path, *path.parents]), 'symlink in input/receipt path')
    need(path.resolve() == path, 'input/receipt canonical path differs')
    need(not os.path.lexists(path) or path.is_file(), 'input/receipt is not a regular file')
    return path


def reference(path, root, d):
    path = checked_path(path, root)
    need(path.is_file(), 'missing receipt: ' + str(path))
    return {'path': str(path), **d.fingerprint(path)}


def read_reference(ref, root, api, d):
    need(reference(Path(ref['path']), root, d) == ref, 'receipt bytes or path changed')
    return api.read_json(ref['path'])


def binary_identity(d):
    path = checked_path(PROJECT / FIXTURE['install_path'], PROJECT)
    need(path.is_file(), 'original cells.npy is absent')
    def stamp():
        stat = path.stat()
        return tuple(getattr(stat, k) for k in
                     ('st_dev', 'st_ino', 'st_size', 'st_mtime_ns', 'st_ctime_ns'))
    before = stamp()
    descriptor = d.fingerprint(path)
    blob = hashlib.sha1(b'blob ' + str(FIXTURE['bytes']).encode() + b'\0')
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            blob.update(chunk)
    need(stamp() == before, 'original binary changed while hashing')
    need(descriptor == {k: FIXTURE[k] for k in ('bytes', 'sha256')} and
         blob.hexdigest() == FIXTURE['git_blob_sha1'], 'original binary bytes differ')
    return {'identity': {'canonical_path': str(path), **descriptor,
                         'git_blob_sha1': blob.hexdigest()}, 'file_state': list(before)}


def source_context(source, h):
    graph, actual = h.project_graph(PROJECT, [MODULE])
    sources = {}
    for module in graph:
        path = checked_path(PROJECT / h.module_path(module), PROJECT)
        payload = git('show', source + ':' + h.module_path(module))
        sources[module] = sha(payload)
        need(actual[module]['sha256'] == sources[module] and
             path.read_bytes() == payload and
             graph[module] == [x for x in h.imports(payload) if x.startswith('ImbalancedChen.')],
             'published dependency source differs: ' + module)
    return graph, sources


def load_spec(source):
    need(re.fullmatch(r'[0-9a-f]{40}', source), 'a full source commit is required')
    script = Path(__file__).read_bytes()
    need(script == git('show', source + ':' + SCRIPT), 'executing adapter is not the published source')
    driver = git('show', source + ':' + DRIVER)
    need(sha(driver) == DRIVER_SHA and
         sha(git('show', source + ':' + MATERIALIZER)) == MATERIALIZER_SHA,
         'the original P1.4 entry points must remain unchanged')
    base = types.ModuleType('unchanged_p14_driver')
    exec(compile(driver, DRIVER, 'exec'), base.__dict__)
    api_bytes = git('show', base.API_COMMIT + ':' + base.API_PATH)
    need(sha(api_bytes) == base.API_SHA, 'original acceptance API differs')
    api = base.load(api_bytes, 'original_npy_existing_api')
    raw = {p: git('show', api.TOOLS + ':' + p) for p in api.PINS}
    need(all(sha(raw[p]) == digest for p, digest in api.PINS.items()), 'original helper pin differs')
    h = base.load(raw[api.HELPER], 'original_npy_helper')
    ops = base.load(raw[api.OPS], 'original_npy_ops')
    d = base.load(raw[api.PRIMITIVES], 'original_npy_primitives')
    manifest_bytes = git('show', source + ':' + MANIFEST)
    manifest = json.loads(manifest_bytes)
    validate_manifest(manifest)
    row = manifest['modules'][0]
    payload = git('show', source + ':' + SOURCE_PATH)
    need(len(payload) == row['bytes'] and sha(payload) == row['sha256'] and
         git('rev-parse', source + ':' + SOURCE_PATH).decode().strip() == row['git_blob_sha1'],
         'consumer Git source differs')
    for commit, path in [(source, FIXTURE['repository_path']),
                         (FIXTURE['origin_commit'], FIXTURE['origin_path'])]:
        need(git('rev-parse', commit + ':' + path).decode().strip() == FIXTURE['git_blob_sha1'],
             'binary is not the retained original Git object')
    registry = manifest['source_registry']
    need(sha(git('show', registry['commit'] + ':' + registry['path'])) == registry['sha256'],
         'historical binary provenance differs')
    need(sha(base.REVIEW.read_bytes()) == base.REVIEW_SHA, 'original runtime review differs')
    review = json.loads(base.REVIEW.read_bytes())
    runtime = d.runtime_binding(h)
    need(runtime == review['existing_runtime_bindings'] and
         {p: d.fingerprint(PROJECT / p) for p in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')}
         == review['runtime_configuration_bindings'] and not (PROJECT / 'lakefile.lean').exists(),
         'original P1 runtime/configuration differs')
    binding = {'source_commit': source, 'adapter_sha256': sha(script), 'manifest_sha256': sha(manifest_bytes),
               'unchanged_driver_sha256': DRIVER_SHA, 'unchanged_materializer_sha256': MATERIALIZER_SHA,
               'api_commit': base.API_COMMIT, 'api_sha256': base.API_SHA, 'helper_pins': api.PINS,
               'consumer': row, 'data_inputs': [FIXTURE], 'runtime': runtime,
               'project': str(PROJECT), 'protected_roots': h.check_roots(), 'whole_P1_4_complete': False}
    data_key = sha(json.dumps([FIXTURE], sort_keys=True).encode())[:20]
    root = base.ROOT / 'original-npy-kernel' / source / data_key
    return api, h, ops, d, raw, payload, binding, root


def phase_record(phase, binding, observed, **extra):
    return {'schema': 'p14_original_npy_phase_v1', 'phase': phase,
            'binding_sha256': sha(json.dumps(binding, sort_keys=True).encode()),
            'source_commit': binding['source_commit'], 'module': MODULE, 'binary': observed, **extra}


def normal_data_valid(root, binding, normal, observed, api, d):
    join = api.read_json(checked_path(root / 'NORMAL_DATA_BINDING.json', root))
    need(join['binding_sha256'] == sha(json.dumps(binding, sort_keys=True).encode()), 'normal data context differs')
    pre = read_reference(join['pre'], root, api, d)
    post = read_reference(join['post'], root, api, d)
    need(pre['phase'] == 'PRE_NORMAL' and post['phase'] == 'POST_NORMAL' and
         pre['binding_sha256'] == post['binding_sha256'] == join['binding_sha256'] and
         pre['prior_normal_present'] is False and post['normal_created_this_attempt'] is True and
         post['normal_error'] is None and
         pre['binary'] == post['binary'] and pre['binary']['identity'] == observed['identity'],
         'missing original compilation-time binary pre/post identity')
    normal_path = root / 'normal' / MODULE / 'NORMAL_PASS.json'
    need(join['normal'] == post['normal'] == reference(normal_path, root, d) and
         normal == api.read_json(normal_path) and
         join['normal_command_sha256'] == normal['normal_command']['command_sha256'] and
         post['source_plus_five_outputs'] == normal['source_plus_five_outputs'],
         'data evidence is not joined to this normal command and object')
    return join


def prior_attempts_complete(root, run, binding, api, d):
    key = sha(json.dumps(binding, sort_keys=True).encode())
    for previous in sorted((root / 'runs').glob('attempt-*')):
        if previous == run:
            continue
        need(previous.is_dir() and not previous.is_symlink(), 'unexpected prior attempt')
        result_path = previous / 'RESULT.json'
        need(result_path.is_file(), 'INTERRUPTED_ATTEMPT_REQUIRES_INSPECTION: ' + str(previous))
        result = api.read_json(result_path)
        need(result['binding_sha256'] == key, 'prior attempt belongs to different inputs')
        # A worker result alone cannot repair an interrupted outer coordinator.
        before, after = previous / 'GIT_BEFORE.json', previous / 'GIT_AFTER.json'
        need(before.is_file() and after.is_file() and api.read_json(before) == api.read_json(after) and
             (previous / 'serialized-worker-command.json').is_file(),
             'INCOMPLETE_OUTER_ATTEMPT_REQUIRES_INSPECTION: ' + str(previous))
        if result['accepted_owners']:
            need((previous / 'DATA_BOUND_ACCEPTANCE.json').is_file(), 'missing outer data-bound acceptance')
        if (previous / 'DATA_PRE_NORMAL.json').exists():
            need((previous / 'DATA_POST_NORMAL.json').is_file(), 'missing original post-normal data receipt')
        if result['audit_started']:
            need((previous / 'DATA_POST_AUDIT.json').is_file(), 'missing original post-audit data receipt')
        for ref in result['data_receipts'].values():
            read_reference(ref, root, api, d)


def audit_references(root, d):
    records = {}
    for directory in sorted((root / 'audits').glob('*')):
        need(directory.is_dir() and not directory.is_symlink(), 'unexpected audit directory')
        names = ['AUDIT_PLAN.json', 'lane-0/VALIDATION_RESULTS.json',
                 'lane-0/OWNED_EXPORTS.json', 'lane-0/all-owned-types-axioms.log']
        records[str(directory)] = {name: reference(directory / name, root, d)
                                   for name in names if (directory / name).is_file()}
    return records


def worker(spec, run):
    api, h, ops, d, raw, payload, binding, root = spec
    d.verify_lane(h)
    need(api.read_json(root / 'BINDING.json') == binding, 'worker binding changed')
    accepted, data_refs, normal, error = set(), {}, None, None
    audit_started = False
    try:
        prior_attempts_complete(root, run, binding, api, d)
        # Existing exact bytes are no-ops. Unknown source/data preimages are rejected.
        source_path = checked_path(PROJECT / SOURCE_PATH, PROJECT)
        d.write_frozen(source_path, payload)
        graph, sources = source_context(binding['source_commit'], h)
        d.save(run / 'PROJECT_SOURCES.json', sources)
        binary_path = checked_path(PROJECT / FIXTURE['install_path'], PROJECT)
        if not binary_path.exists():
            binary = git('cat-file', 'blob', FIXTURE['git_blob_sha1'])
            need(len(binary) == FIXTURE['bytes'] and sha(binary) == FIXTURE['sha256'], 'Git binary bytes differ')
            d.write_frozen(binary_path, binary)
        before = binary_identity(d)
        normal_path = root / 'normal' / MODULE / 'NORMAL_PASS.json'
        prior = api.read_json(normal_path) if normal_path.exists() else None
        if prior is not None:
            normal_data_valid(root, binding, prior, before, api, d)
        else:
            need(not (root / 'NORMAL_DATA_BINDING.json').exists(), 'data join without its original normal')
        pre_path = run / 'DATA_PRE_NORMAL.json'
        d.save(pre_path, phase_record('PRE_NORMAL', binding, before, prior_normal_present=prior is not None))
        data_refs['pre_normal'] = reference(pre_path, root, d)
        normal_error = None
        try:
            normal = api.normal_one(binding['source_commit'], PROJECT, root, MODULE, graph, sources, h, ops, d)
        except Exception as exc:
            normal_error = str(exc)
        after_normal = binary_identity(d)
        need(after_normal == before, 'binary changed during normal')
        post_path = run / 'DATA_POST_NORMAL.json'
        d.save(post_path, phase_record('POST_NORMAL', binding, after_normal,
               normal_created_this_attempt=prior is None and normal is not None,
               normal=reference(normal_path, root, d) if normal is not None else None,
               source_plus_five_outputs=d.snapshot(PROJECT, MODULE) if normal is not None else None,
               normal_error=normal_error))
        data_refs['post_normal'] = reference(post_path, root, d)
        need(normal_error is None and normal is not None, 'NORMAL_HELD_OR_FAILED: ' + str(normal_error))
        need(d.snapshot(PROJECT, MODULE) == normal['source_plus_five_outputs'], 'normal object changed')
        if prior is None:
            d.save(root / 'NORMAL_DATA_BINDING.json', {
                'schema': 'p14_original_npy_normal_data_join_v1',
                'binding_sha256': sha(json.dumps(binding, sort_keys=True).encode()),
                'pre': data_refs['pre_normal'], 'post': data_refs['post_normal'],
                'normal': reference(normal_path, root, d),
                'normal_command_sha256': normal['normal_command']['command_sha256']})
        normal_data_valid(root, binding, normal, after_normal, api, d)
        audit_started = True
        audit_error = None
        try:
            # Retain the original partial-audit hold; never remove or reroot an audit.
            api.audit(binding['source_commit'], PROJECT, root, {MODULE: normal},
                      graph, sources, h, ops, d, run, accepted)
        except Exception as exc:
            audit_error = str(exc)
        after_audit = binary_identity(d)
        need(after_audit == before, 'binary changed during kernel/full-owned audit')
        need(d.snapshot(PROJECT, MODULE) == normal['source_plus_five_outputs'], 'audited object changed')
        audit_refs = audit_references(root, d)
        audit_post_path = run / 'DATA_POST_AUDIT.json'
        d.save(audit_post_path, phase_record('POST_AUDIT', binding, after_audit,
               normal_data_binding=reference(root / 'NORMAL_DATA_BINDING.json', root, d),
               normal=reference(normal_path, root, d), audits=audit_refs,
               source_plus_five_outputs=d.snapshot(PROJECT, MODULE), audit_error=audit_error))
        data_refs['post_audit'] = reference(audit_post_path, root, d)
        need(audit_error is None and accepted == {MODULE}, 'AUDIT_HELD_OR_FAILED: ' + str(audit_error))
        normal_data_valid(root, binding, normal, after_audit, api, d)
        need(h.check_roots() == binding['protected_roots'] and d.runtime_binding(h) == binding['runtime'],
             'protected roots/runtime changed')
        d.save(run / 'DATA_BINDING_COMPLETE.json', {
            'schema': 'p14_original_npy_worker_data_binding_v1',
            'status': 'DATA_BOUND_WORKER_COMPLETE_OUTER_ACCEPTANCE_PENDING',
            'requires_outer_acceptance': True,
            'binding': reference(root / 'BINDING.json', root, d),
            'data_receipts': data_refs, 'normal_data_binding': reference(root / 'NORMAL_DATA_BINDING.json', root, d),
            'normal': reference(normal_path, root, d), 'audits': audit_refs,
            'source_plus_five_outputs': normal['source_plus_five_outputs'],
            'accepted_owners': [MODULE], 'whole_P1_4_complete': False})
    except Exception as exc:
        error = str(exc)
        accepted.clear()
    result = {'source_commit': binding['source_commit'],
              'binding_sha256': sha(json.dumps(binding, sort_keys=True).encode()),
              'module': MODULE, 'audit_started': audit_started, 'data_receipts': data_refs,
              'accepted_owners': sorted(accepted) if error is None else [],
              'normal_receipt_present': (root / 'normal' / MODULE / 'NORMAL_PASS.json').is_file(),
              'error': error, 'whole_P1_4_complete': False}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result), flush=True)
    return 0 if error is None and accepted == {MODULE} else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--worker', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    spec = load_spec(args.source_commit)
    api, h, ops, d, raw, payload, binding, root = spec
    if args.check:
        need(args.worker is None, '--check cannot be a worker')
        source_path = checked_path(PROJECT / SOURCE_PATH, PROJECT)
        binary_path = checked_path(PROJECT / FIXTURE['install_path'], PROJECT)
        if source_path.exists():
            need(source_path.read_bytes() == payload, 'unknown existing consumer source')
            source_context(args.source_commit, h)
        observed = binary_identity(d) if binary_path.exists() else None
        print(json.dumps({'status': 'READ_ONLY_INPUT_CHECK_NOT_ACCEPTANCE', 'source_commit': args.source_commit,
                          'source_present': source_path.exists(), 'binary': observed, 'whole_P1_4_complete': False}))
        return 0
    if args.worker is not None:
        run = args.worker.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid serialized worker directory')
        return worker(spec, run)
    original = d.original_git_state(REPO)
    d.save(checked_path(root / 'BINDING.json', root), binding)
    d.write_frozen(root / 'inputs/e9.py', raw[api.E9])
    executed = root / 'executed-original-npy.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--source-commit', args.source_commit, '--run', '--worker', str(run)]
    command = None
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', child),
                          cwd=PROJECT, relay=True)
    finally:
        after = d.original_git_state(REPO)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original source Git checkout changed')
    need(command is not None, 'missing serialized worker completion')
    if command['exit_code'] != 0:
        return command['exit_code']
    result = api.read_json(run / 'RESULT.json')
    need(result['error'] is None and result['accepted_owners'] == [MODULE], 'worker did not complete data binding')
    d.save(run / 'DATA_BOUND_ACCEPTANCE.json', {
        'schema': 'p14_original_npy_data_bound_acceptance_v1',
        'status': 'ORIGINAL_NPY_NORMAL_KERNEL_FULL_OWNED_DATA_BOUND',
        'source_commit': args.source_commit,
        'binding': reference(root / 'BINDING.json', root, d),
        'worker_data_binding': reference(run / 'DATA_BINDING_COMPLETE.json', root, d),
        'worker_result': reference(run / 'RESULT.json', root, d),
        'serializer_command': reference(run / 'serialized-worker-command.json', root, d),
        'serializer_log': reference(run / 'serialized-worker.log', root, d),
        'validation_lane': reference(run / 'VALIDATION_LANE.json', root, d),
        'git_before': reference(run / 'GIT_BEFORE.json', root, d),
        'git_after': reference(run / 'GIT_AFTER.json', root, d),
        'accepted_owners': [MODULE], 'whole_P1_4_complete': False})
    print(json.dumps({'status': 'ORIGINAL_NPY_NORMAL_KERNEL_FULL_OWNED_DATA_BOUND',
                      'acceptance': str(run / 'DATA_BOUND_ACCEPTANCE.json'),
                      'whole_P1_4_complete': False}), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
