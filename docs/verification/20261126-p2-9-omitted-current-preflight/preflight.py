#!/usr/bin/env python3
"""Bounded current-P2 metadata and five exact Lake facets; no Lean or writes."""
import base64
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

sys.dont_write_bytecode = True
TC = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
CONFIG_ROOTS = [Path('/workspace/goldbach-p2'), Path('/workspace/p2-saving16-20261125')]
GUARD_CANDIDATE_ROOT = Path('/workspace/blue-build-tools')
ACTION_CANDIDATE = GUARD_CANDIDATE_ROOT / 'lean-action'
ACTION_COMMIT = 'f061402b660e0c34644504b324e830f2991d4865'
MAX_FILE_BYTES = 262144
MAX_OUTPUT_BYTES = 1800000
READ_IDENTITIES = {}
HASHED_PATHS = {}
RESULT = {'schema': 'p29_omitted_current_P2_config_resource_Lake5_preflight_v1',
          'scope': {'Lean_invocations': 0, 'filesystem_writes': 0,
                    'old_normal_or_kernel_owned_replays': 0,
                    'old_project54_source_object_inventory_reads': 0,
                    'old_snapshot_or_P1_P3_graph_reads': 0,
                    'foreign18_object_contents_reread': 0,
                    'new_actual_import_graph_qualified': False,
                    'new_formal_credit': 0}}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def stat7(s):
    return [s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def metadata(path):
    path = Path(path)
    try:
        entry = path.lstat()
    except FileNotFoundError:
        return {'path': str(path), 'status': 'NO_ENTRY_AT_THIS_EXACT_PATH'}
    result = {'path': str(path), 'lstat': stat7(entry), 'is_symlink': stat.S_ISLNK(entry.st_mode)}
    if result['is_symlink']:
        result['symlink_text'] = os.readlink(path)
    try:
        final = path.stat()
    except FileNotFoundError:
        result['status'] = 'DANGLING_AT_THIS_EXACT_PATH'
        return result
    result.update(status='EXISTS', resolved_path=str(path.resolve()), stat=stat7(final),
                  is_file=stat.S_ISREG(final.st_mode), is_directory=stat.S_ISDIR(final.st_mode))
    return result


def original_file(path, expected=None, include_bytes=False, limit=MAX_FILE_BYTES):
    path = Path(path)
    before = metadata(path)
    if before['status'] != 'EXISTS' or not before.get('is_file'):
        return before
    if before['stat'][4] > limit:
        return {**before, 'content_status': 'NOT_READ_OVER_EXPLICIT_BYTE_LIMIT', 'limit_bytes': limit}
    raw = path.read_bytes()
    require(metadata(path) == before and len(raw) == before['stat'][4], 'changed during read: ' + str(path))
    row = {**before, 'content_status': 'COMPLETE_ORIGINAL_READ', 'bytes': len(raw), 'sha256': sha(raw)}
    if expected is not None:
        row['expected_sha256'] = expected
        row['expected_hash_matches'] = row['sha256'] == expected
    if include_bytes:
        row['content_base64'] = base64.b64encode(raw).decode('ascii')
    READ_IDENTITIES[str(path)] = before
    HASHED_PATHS[str(path)] = row['sha256']
    return row


def git_metadata(path):
    path = Path(path)
    if not path.is_dir():
        return {'path': str(path), 'status': 'NO_DIRECTORY_AT_THIS_EXACT_PATH'}
    result = {'path': str(path), 'resolved_path': str(path.resolve()), 'commands': []}
    for args in [('rev-parse', '--show-toplevel'), ('rev-parse', 'HEAD')]:
        command = ['git', '-C', str(path), *args]
        p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           env={**os.environ, 'GIT_OPTIONAL_LOCKS': '0'}, timeout=15)
        require(len(p.stdout) + len(p.stderr) <= 32768, 'unexpected git metadata output size')
        result['commands'].append({'command': command, 'exit_code': p.returncode,
                                   'stdout': p.stdout.decode('utf-8', 'replace'),
                                   'stderr': p.stderr.decode('utf-8', 'replace')})
    result['status'] = 'EXACT_GIT_METADATA_READ' if all(r['exit_code'] == 0 for r in result['commands']) else 'GIT_METADATA_UNAVAILABLE'
    return result


def read_proc(path, limit=65536):
    with Path(path).open('rb') as stream:
        raw = stream.read(limit + 1)
    require(len(raw) <= limit, 'proc metadata limit exceeded: ' + path)
    return raw


def main():
    require(isinstance(INPUTS_RAW, bytes) and sha(INPUTS_RAW) == INPUTS_SHA256,
            'fixed pure-data inputs changed')
    inputs = json.loads(INPUTS_RAW)
    require(inputs['schema'] == 'p29_omitted_preflight_fixed_local_inputs_v1', 'wrong input schema')
    receiver_raw = base64.b64decode(inputs['receiver_binding_base64'], validate=True)
    require(sha(receiver_raw) == 'ccec77943f9a98e1fca5dbe8264bd7d90be0c5e90962c27ef06ac4315b5251b7',
            'accepted receiver table changed')
    receiver = json.loads(receiver_raw)
    require(receiver['status'] == 'PASS_BYTE_RECEPTION_ONLY' and len(receiver['selected_objects']) == 18,
            'unexpected received-object table')
    shape_raw = base64.b64decode(inputs['snapshot_shape_base64'], validate=True)
    require(sha(shape_raw) == inputs['snapshot_shape_sha256'], 'accepted snapshot shape changed')
    shape = json.loads(shape_raw)
    require(shape['raw_source']['sha256'] == 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
            and shape['runtime']['lean'] == str(TC / 'bin/lean'), 'unexpected original runtime')
    RESULT['started_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    RESULT['fixed_inputs_sha256'] = INPUTS_SHA256
    RESULT['input_origin'] = inputs['input_origin']
    RESULT['scope']['foreign18_expected_receipt_hash_is_not_recomputed_from_object_contents'] = True
    proc_cgroup = read_proc('/proc/self/cgroup')
    mountinfo = read_proc('/proc/self/mountinfo')
    mem_raw = read_proc('/proc/meminfo')
    mem = {k: int(v.split()[0]) * 1024 for k, v in (line.split(':', 1) for line in mem_raw.decode().splitlines())}
    disk = shutil.disk_usage('/workspace')
    RESULT['resources'] = {
        'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'pid': os.getpid(), 'cpu_affinity': sorted(os.sched_getaffinity(0)),
        'workspace_disk': {'total': disk.total, 'used': disk.used, 'free': disk.free},
        'host_MemAvailable_bytes': mem['MemAvailable'],
        'host_meminfo_sha256': sha(mem_raw),
        'proc_self_cgroup_text': proc_cgroup.decode(), 'mountinfo_sha256': sha(mountinfo),
        'cgroup2_mountinfo_rows': [line for line in mountinfo.decode().splitlines() if ' - cgroup2 ' in line],
        'cgroup_namespace': os.readlink('/proc/self/ns/cgroup'),
        'pid_namespace': os.readlink('/proc/self/ns/pid'),
        'future_guard_policy': 'Lean -t0 -j2 -M12288; native checker LEAN_NUM_THREADS=2',
        'this_readonly_task_does_not_prove_future_2_thread_allocation': True,
        'service_enforcement_basis': 'CPU affinity; aggregate process-tree RSS sampled every 50 ms; PID namespace teardown',
        'not_a_hard_cgroup_reservation_or_OOM_guarantee': True,
        'environment_headroom_not_inferred_from_host_cache': True}
    lake_rows = inputs['Lake_Util_Casing_five_facets']
    require(len(lake_rows) == 5 and {r['facet'] for r in lake_rows} ==
            {'.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'}, 'wrong exact Lake subset')
    RESULT['Lake_Util_Casing'] = []
    for row in lake_rows:
        require(row['module'] == 'Lake.Util.Casing', 'unrelated facet candidate')
        expected_path = TC / ('lib/lean/Lake/Util/Casing' + row['facet'])
        require(row['P1_required']['path'] == str(expected_path), 'candidate not supplied by accepted delta')
        record = original_file(expected_path, row['P1_required']['sha256'])
        if record.get('content_status') == 'COMPLETE_ORIGINAL_READ':
            record['expected_bytes_match'] = record['bytes'] == row['P1_required']['bytes']
        RESULT['Lake_Util_Casing'].append({'module': row['module'], 'facet': row['facet'],
                                         'original_required': row['P1_required'], 'current': record})
    RESULT['received18_identity_only'] = []
    for row in receiver['selected_objects']:
        path = Path(row['path'])
        require(path.is_relative_to('/workspace/p29-omitted-inputs-20261126-b23868d'),
                'receiver path outside the accepted exclusive root')
        current = metadata(path)
        record = {'module': row['module'], 'recorded_bytes': row['bytes'], 'recorded_sha256': row['sha256'],
                  'recorded_stat': row['stat'], 'current': current,
                  'current_stat_matches_received_stat': current.get('stat') == row['stat'],
                  'object_contents_read': False}
        if row.get('source'):
            source = row['source']
            require(Path(source['path']).is_relative_to('/workspace/p29-omitted-inputs-20261126-b23868d'),
                    'received source outside the accepted exclusive root')
            sm = metadata(source['path'])
            record['source_identity_only'] = {'recorded': source, 'current': sm,
                                             'current_stat_matches_received_stat': sm.get('stat') == source['stat']}
        RESULT['received18_identity_only'].append(record)
    RESULT['project_configuration_candidates'] = {}
    for root in CONFIG_ROOTS:
        RESULT['project_configuration_candidates'][str(root)] = {
            'root': metadata(root),
            'files': {name: original_file(root / name, include_bytes=True)
                      for name in ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json']},
            'package_directory': metadata(root / '.lake/packages'),
            'git': git_metadata(root)}
    RESULT['original_snapshot_search_roots'] = [metadata(path) for path in shape['runtime']['lean_path']]
    package_roots = {}
    for path in shape['runtime']['lean_path']:
        p = Path(path)
        if p.parts[-4:] == ('.lake', 'build', 'lib', 'lean'):
            root = p.parents[3]
            package_roots.setdefault(str(root.resolve()), root)
    RESULT['current_package_git'] = {key: git_metadata(path) for key, path in package_roots.items()}
    RESULT['runtime_files'] = {name: original_file(TC / 'bin' / name, pin, limit=33554432)
                               for name, pin in inputs['accepted_runtime_pins'].items()}
    RESULT['runtime_tool_identity_only'] = {name: metadata(TC / 'bin' / name)
                                          for name in ['leanir', 'clang', 'leanc', 'llvm-ar']}
    RESULT['elan_candidates'] = {str(p): metadata(p) for p in
        [Path('/workspace/.elan/bin/elan'), Path('/workspace/.compile-home/.elan/bin/elan'),
         Path('/workspace/.elan/toolchains/leanprover--lean4---v4.33.0-rc1'),
         Path('/workspace/.compile-home/.elan/toolchains/leanprover--lean4---v4.33.0-rc1')]}
    RESULT['elan_on_current_PATH'] = shutil.which('elan')
    RESULT['original_guard_candidates'] = {
        name: original_file(GUARD_CANDIDATE_ROOT / name, digest)
        for name, digest in inputs['original_guard_pins'].items()}
    RESULT['guard_candidate_path_basis'] = 'Existing fixed P1 controller locator; P2 existence is tested only at these exact paths, not assumed.'
    action = {'root': metadata(ACTION_CANDIDATE), 'git': git_metadata(ACTION_CANDIDATE), 'scripts': {}}
    if action['git']['status'] == 'EXACT_GIT_METADATA_READ':
        head = action['git']['commands'][1]['stdout'].strip()
        action['expected_revision_matches'] = head == ACTION_COMMIT
        if head == ACTION_COMMIT:
            action['scripts'] = {name: original_file(ACTION_CANDIDATE / 'scripts' / name, digest)
                                 for name, digest in inputs['original_action_script_pins'].items()}
    RESULT['original_action_candidate'] = action
    for path, before in READ_IDENTITIES.items():
        require(metadata(path) == before, 'file identity changed across preflight: ' + path)
    RESULT['read_original_files_still_same_identity'] = True
    RESULT['complete_file_reads'] = [{'path': path, 'sha256': digest} for path, digest in HASHED_PATHS.items()]
    RESULT['status'] = 'BOUNDED_CURRENT_METADATA_CAPTURED_NOT_A_NEW_IMPORT_OR_PROOF_QUALIFICATION'
    RESULT['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    raw = json.dumps(RESULT, sort_keys=True, separators=(',', ':')).encode()
    require(len(raw) + 64 <= MAX_OUTPUT_BYTES, 'bounded result exceeds declared stdout budget')
    print('P29_OMITTED_PREFLIGHT ' + raw.decode(), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        RESULT['status'] = 'PREFLIGHT_FAILED_NO_WRITES_OR_LEAN'
        RESULT['error'] = type(exc).__name__ + ': ' + str(exc)
        fallback = json.dumps(RESULT, sort_keys=True, separators=(',', ':')).encode()
        if len(fallback) + 64 <= MAX_OUTPUT_BYTES:
            print('P29_OMITTED_PREFLIGHT ' + fallback.decode(), flush=True)
        else:
            print(json.dumps({'status': RESULT['status'], 'error': RESULT['error'],
                              'captured_result_bytes': len(fallback), 'full_result_not_emitted': True}), flush=True)
        raise
