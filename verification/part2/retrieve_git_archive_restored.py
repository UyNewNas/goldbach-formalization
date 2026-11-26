#!/usr/bin/env python3
"""Retrieve the authorized P2.1 evidence archive from its exact published Git tree.

Restored implementation, 2026-11-26. The former temporary script was not recovered;
its historical SHA and test result are not claimed for this source. This program
does no compilation, remote write, ref update, or MCP-capture fabrication. Explicit
fetches use only the fixed public repository; all local object reads disable lazy
fetch. Original Git stdout/stderr and return codes are retained, including the full
binary cat-file stdout, which is streamed to the audit directory in /dev/shm.
The four pinned manifests preserve the original 140-source P2.1 scope. Successful
retrieval is byte-transport verification only; the unchanged repack verifier is a
separate gate and no result here establishes full P2 or new Lean proof credit.
"""
import argparse
from contextlib import contextmanager
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
import time
import types

REMOTE = 'https://github.com/UyNewNas/goldbach-formalization.git'
EVIDENCE_REF = 'refs/heads/evidence/p2-1-20261126-6c7864ad'
COMMIT = '947a5dd8fb3c32c8a2688b767f559d7ab31d46d1'
TREE = '14b67d3e5a4435fb02046d7d541e0d5531aff719'
PARENT = '48b343279639cb3a289628d35cc23b2710eedd05'
ACCEPTED = '1de0453bee55bf1128be422787216937b8fda9c9'
ACCEPTED_TREE = 'af74f02d263c72b0bb8e003ce49d1134ac04c5d5'
SOURCE_SNAPSHOT = '00af18335dcebcc5e24571e33be7791ff718fbff'
# The helper digest below is the frozen original producer, not this restoration.
HELPER_SHA = '5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d'
BASE = 'docs/verification/20261126-p2-1'
PLAN_PATH = BASE + '/DIRECT_GIT_PLAN.json'
MANIFEST_PATH = BASE + '/ARCHIVE_PARTS.json'
PLAN_BINDING = (124473, 'ac1d24aaf71dbc1f5cf89f8ab205f25fd58d8689726c81337a2499666bae068b',
                '3e434e0a01326d10389f7a5129c8896eecac1219')
MANIFEST_BINDING = (124749, '9dcbcd975650891e0f6e50514f80bc67fb2152fec382307b3ca1128bb79ede42',
                    '044ba48dde1c35bb04f6fe29aba23de418ce54e1')
METADATA_BINDINGS = {
    PLAN_PATH: PLAN_BINDING,
    MANIFEST_PATH: MANIFEST_BINDING,
    BASE + '/LOSSLESS_ASSETS.json': (87516, 'a626035527192dce8770d9754a99c4ce5bbadd5ebaa809f13102fe69bc17dd5d',
                                    '57cc0a99973675a0bb039182d588c0ae54dc80a9'),
    BASE + '/TRANSPORT_METHOD.json': (55467, '19afb2d83ea564c171252b3b533495934201c8f26f839d25b01d127bb14b5c67',
                                     'e62a504a42e40b514a7a436b81d327e98c1c2127'),
}
ASSET_NAMES = {'export_manifest': 'export-manifest.json.xz', 'joint_receipt': 'joint-receipt.json.xz',
               'joint_log': 'joint.log.xz', 'joint_probe': 'Joint.lean.xz', 'finalization': 'FINALIZATION.json.xz',
               'verification': 'verification.json.xz', 'retention': 'PERSISTENT_COPY.json.xz'}
WHOLE = (490564596, '066a46e41e34578a2adbf2a1120e8aba0470dfde44d6052bc8576d8fcb9aa212')
PART_COUNT = 409
PART_BYTES = 1200000
ROUTING_ENV = {'GIT_DIR', 'GIT_WORK_TREE', 'GIT_COMMON_DIR', 'GIT_INDEX_FILE',
               'GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES',
               'GIT_NAMESPACE', 'GIT_PREFIX', 'GIT_CURL_VERBOSE'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def raw_sha(data):
    return hashlib.sha256(data).hexdigest()


def stable_stat(info):
    return tuple(getattr(info, key) for key in ('st_dev', 'st_ino', 'st_mode', 'st_nlink',
                                               'st_size', 'st_mtime_ns', 'st_ctime_ns'))


def load_helper(path):
    require(path.is_absolute() and path.resolve(strict=True) == path, 'Helper path is redirected')
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'Helper is not a regular file')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as source:
        raw = source.read()
        require(stable_stat(os.fstat(source.fileno())) == stable_stat(before)
                and stable_stat(path.lstat()) == stable_stat(before), 'Helper changed while reading')
    require(raw_sha(raw) == HELPER_SHA, 'Frozen original helper SHA differs')
    module = types.ModuleType('p21_frozen_transfer_helper')
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def write_all(stream, data):
    remaining = memoryview(data)
    while remaining:
        count = stream.write(remaining)
        require(isinstance(count, int) and count > 0, 'Short/zero output write')
        remaining = remaining[count:]


def open_output(fd):
    return os.fdopen(fd, 'wb', buffering=0)


class CapturedReader:
    def __init__(self, source, capture):
        self.source, self.capture = source, capture
        self.digest, self.count = hashlib.sha256(), 0
        self.capture_error = None

    def record(self, raw):
        self.digest.update(raw)
        self.count += len(raw)
        if self.capture_error is None:
            try:
                write_all(self.capture, raw)
            except BaseException as error:
                self.capture_error = error
                raise
        return raw

    def read(self, count):
        return self.record(self.source.read(count))

    def readline(self, limit):
        return self.record(self.source.readline(limit))


class AuditedGit:
    def __init__(self, repository, audit, helper):
        self.repository, self.audit, self.helper = repository, audit, helper
        audit.mkdir(mode=0o700)
        self.records = []
        self.environment = {key: value for key, value in os.environ.items()
                            if key not in ROUTING_ENV and not key.startswith('GIT_TRACE')}
        self.environment.update(GIT_TERMINAL_PROMPT='0', GIT_NO_LAZY_FETCH='1')

    def argv(self, arguments, with_repository=True):
        command = ['git', '--no-lazy-fetch', '--no-replace-objects', '--literal-pathspecs',
                   '-c', 'gc.auto=0', '-c', 'pack.threads=1']
        if with_repository:
            command.extend(['-C', str(self.repository)])
        return command + list(arguments)

    def file_binding(self, path):
        size, digest = self.helper.digest_file(path)
        return {'path': str(path), 'bytes': size, 'sha256': digest}

    def run(self, arguments, stdin=b'', with_repository=True, consumer=None, return_path=False):
        stem = self.audit / f'{len(self.records):03d}'
        input_path, output_path, error_path = (Path(str(stem) + suffix)
                                               for suffix in ('.stdin.bin', '.stdout.bin', '.stderr.bin'))
        input_path.write_bytes(stdin)
        argv = self.argv(arguments, with_repository)
        start = time.time()
        record = {'argv': argv, 'started_unix': start, 'explicit_network_command': bool(arguments and arguments[0] in ('fetch', 'ls-remote')),
                  'git_config_environment_preserved': True, 'script_disables_system_or_global_config': False,
                  'performance_config_overrides': {'gc.auto': '0', 'pack.threads': '1'},
                  'implicit_lazy_fetch_disabled': True,
                  'repository_environment_removed': sorted(ROUTING_ENV), 'trace_environment_removed': True,
                  'stdin': self.file_binding(input_path)}
        primary = None
        result = None
        process = reader = None
        try:
            with input_path.open('rb') as source, output_path.open('xb', buffering=0) as capture, error_path.open('xb', buffering=0) as errors:
                process = subprocess.Popen(argv, stdin=source, stdout=subprocess.PIPE, stderr=errors,
                                           env=self.environment, close_fds=True)
                reader = CapturedReader(process.stdout, capture)
                try:
                    if consumer is None:
                        while reader.read(262144):
                            pass
                    else:
                        result = consumer(reader)
                except BaseException as error:
                    primary = error
                    if process.poll() is None:
                        process.terminate()
                finally:
                    # Retain every byte actually emitted, even after validation failed.
                    try:
                        while reader.read(262144):
                            pass
                    except BaseException as error:
                        if primary is None:
                            primary = error
                        if process.poll() is None:
                            process.kill()
                        while True:
                            raw = process.stdout.read(262144)
                            if not raw:
                                break
                            reader.digest.update(raw)
                            reader.count += len(raw)
                    process.stdout.close()
                    record['exit_code'] = process.wait()
        except BaseException as error:
            if primary is None:
                primary = error
        finally:
            record['finished_unix'] = time.time()
            record.setdefault('exit_code', None)
            for key, path in [('stdout', output_path), ('stderr', error_path)]:
                if path.exists():
                    record[key] = self.file_binding(path)
            if reader is not None:
                record['stdout_stream'] = {'bytes': reader.count, 'sha256': reader.digest.hexdigest()}
                record['stdout_complete'] = (record.get('stdout', {}).get('bytes') == reader.count
                                              and record.get('stdout', {}).get('sha256') == reader.digest.hexdigest()
                                              and reader.capture_error is None)
            else:
                record['stdout_complete'] = False
            if primary is not None:
                record['failure'] = f'{type(primary).__name__}: {primary}'
            self.records.append(record)
            Path(str(stem) + '.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
        if primary is not None:
            raise primary
        require(record['exit_code'] == 0, f'Git command failed; inspect {error_path}')
        require(record['stdout_complete'], 'Git stdout capture is incomplete')
        if consumer is not None:
            return result
        if return_path:
            return output_path
        require(record['stdout']['bytes'] <= 2000000, 'Unexpectedly large metadata stdout')
        return output_path.read_bytes()

    def fetch(self, objects):
        require(objects and all(re.fullmatch('[0-9a-f]{40}', item) for item in objects), 'Unsafe fetch object')
        return self.run(['fetch', '--no-auto-gc', '--no-tags', '--no-prune', '--no-prune-tags',
                         '--no-write-fetch-head', '--no-recurse-submodules', '--no-write-commit-graph',
                         '--refmap=', '--filter=blob:none', '--depth=1', 'origin', *objects])


def validate_layout(parts, expected):
    require(isinstance(parts, list) and parts, 'Archive has no parts')
    offset = 0
    for index, part in enumerate(parts):
        require(type(part['index']) is int and type(part['offset']) is int
                and part['index'] == index and part['offset'] == offset, 'Part index/offset is discontinuous')
        require(type(part['bytes']) is int and 0 < part['bytes'] <= PART_BYTES, 'Invalid part size')
        require(re.fullmatch('[0-9a-f]{64}', part['sha256']) is not None
                and re.fullmatch('[0-9a-f]{40}', part['git_blob_sha']) is not None, 'Invalid part digest')
        offset += part['bytes']
    require(offset == expected[0], 'Part byte total differs')


def check_destination(output, expected, helper):
    require(output.is_absolute() and output.parent.resolve(strict=True) == output.parent, 'Output parent is redirected')
    exists = os.path.lexists(output)
    if exists:
        require(helper.digest_file(output) == expected, 'Existing output differs; refusing overwrite')
    return exists


@contextmanager
def verified_output(output, expected, helper):
    exists = check_destination(output, expected, helper)
    partial = destination = own_inode = None
    primary = None
    try:
        if not exists:
            fd, name = tempfile.mkstemp(prefix=output.name + '.', suffix='.partial', dir=output.parent)
            partial = Path(name)
            own_inode = (os.fstat(fd).st_dev, os.fstat(fd).st_ino)
            destination = open_output(fd)

        yield destination, exists
        if destination is not None:
            closing, destination = destination, None
            closing.close()
        require(helper.digest_file(output if exists else partial) == expected, 'Full original readback differs')
        if not exists:
            current = partial.lstat()
            require((current.st_dev, current.st_ino) == own_inode, 'Owned partial was replaced')
            os.link(partial, output, follow_symlinks=False)
        require(helper.digest_file(output) == expected, 'Final output readback differs')
    except BaseException as error:
        primary = error
        raise
    finally:
        cleanup_errors = []
        if destination is not None:
            try:
                destination.close()
            except BaseException as error:
                cleanup_errors.append(error)
        if partial is not None and os.path.lexists(partial):
            try:
                current = partial.lstat()
                require((current.st_dev, current.st_ino) == own_inode, 'Owned partial was replaced; refusing cleanup')
                partial.unlink()
            except BaseException as error:
                cleanup_errors.append(error)
        if cleanup_errors:
            if primary is not None:
                for error in cleanup_errors:
                    primary.add_note(f'Cleanup: {type(error).__name__}: {error}')
            else:
                raise cleanup_errors[0]


def assemble(git, parts, expected, output, helper):
    validate_layout(parts, expected)
    receipts, whole, count = [], hashlib.sha256(), 0
    with verified_output(output, expected, helper) as (destination, exists):
        def consume(reader):
            nonlocal count
            for part in parts:
                expected_header = f"{part['git_blob_sha']} blob {part['bytes']}\n".encode('ascii')
                require(reader.readline(160) == expected_header, f"Batch header differs at part {part['index']}")
                digest = hashlib.sha256()
                git_digest = hashlib.sha1(f"blob {part['bytes']}\0".encode('ascii'))
                remaining = part['bytes']
                while remaining:
                    raw = reader.read(min(262144, remaining))
                    require(bool(raw), f"Truncated part {part['index']}")
                    if destination is not None:
                        write_all(destination, raw)
                    digest.update(raw)
                    git_digest.update(raw)
                    whole.update(raw)
                    count += len(raw)
                    remaining -= len(raw)
                require(reader.read(1) == b'\n', f"Missing batch separator at part {part['index']}")
                require(digest.hexdigest() == part['sha256'] and git_digest.hexdigest() == part['git_blob_sha'],
                        f"Part digest differs at part {part['index']}")
                receipts.append({**part, 'status': 'VERIFIED_GIT_BLOB_BYTES'})
            require(reader.read(1) == b'', 'Unexpected extra batch stdout')

        requests = ''.join(part['git_blob_sha'] + '\n' for part in parts).encode('ascii')
        git.run(['cat-file', '--batch'], stdin=requests, consumer=consume)
        require((count, whole.hexdigest()) == expected, 'Whole archive digest differs')
    return {'path': str(output), 'bytes': count, 'sha256': whole.hexdigest(),
            'status': 'REUSED_WITH_VERIFIED_GIT_BYTES' if exists else 'VERIFIED_REASSEMBLED_ORIGINAL',
            'verified_parts': receipts, 'full_readback_helper_sha256': HELPER_SHA}


def restore_original(stored, parts, expected, output, helper):
    validate_layout(parts, expected)
    receipts, whole, count = [], hashlib.sha256(), 0
    with verified_output(output, expected, helper) as (destination, exists):
        source, before = helper.regular(stored)
        with source:
            with lzma.LZMAFile(source, 'rb') as decoded:
                for part in parts:
                    raw = decoded.read(part['bytes'])
                    require(len(raw) == part['bytes'] and raw_sha(raw) == part['sha256']
                            and helper.blob_sha(raw) == part['git_blob_sha'], 'Original xz part digest differs')
                    if destination is not None:
                        write_all(destination, raw)
                    whole.update(raw)
                    count += len(raw)
                    receipts.append({**part, 'status': 'VERIFIED_DECOMPRESSED_ORIGINAL_PART'})
                require(decoded.read(1) == b'', 'Original xz has extra decoded bytes')
            helper.unchanged(stored, source, before)
        require((count, whole.hexdigest()) == expected, 'Decoded original whole digest differs')
    return {'path': str(output), 'bytes': count, 'sha256': whole.hexdigest(),
            'status': 'REUSED_WITH_VERIFIED_LOSSLESS_BYTES' if exists else 'VERIFIED_LOSSLESS_ORIGINAL',
            'verified_parts': receipts, 'full_readback_helper_sha256': HELPER_SHA}


def check_stored_blob(path, descriptor, helper):
    require(helper.digest_file(path) == (descriptor['bytes'], descriptor['sha256']), 'Stored xz bytes/SHA256 differ')
    digest = hashlib.sha1(f"blob {descriptor['bytes']}\0".encode('ascii'))
    source, before = helper.regular(path)
    with source:
        while raw := source.read(262144):
            digest.update(raw)
        helper.unchanged(path, source, before)
    require(digest.hexdigest() == descriptor['git_blob_sha'], 'Stored xz Git blob digest differs')


def parse_tree(raw):
    rows = {}
    for record in raw.split(b'\0'):
        if not record:
            continue
        metadata, path = record.split(b'\t', 1)
        mode, kind, oid = metadata.decode('ascii').split(' ')
        path = path.decode('utf-8')
        require(mode == '100644' and kind == 'blob' and path not in rows, 'Unexpected tree row')
        rows[path] = oid
    return rows


def validate_metadata(plan, manifest, rows):
    require(plan['synthetic_test_only'] is False and plan['producer_sha256'] == HELPER_SHA, 'Plan is not frozen production evidence')
    require(plan['git_commit'] == ACCEPTED and plan['git_tree'] == ACCEPTED_TREE
            and plan['source_snapshot_commit'] == SOURCE_SNAPSHOT, 'Plan source bindings differ')
    archive = plan['assets']['archive']
    require((archive['bytes'], archive['sha256']) == WHOLE, 'Plan whole archive binding differs')
    require(manifest['schema'] == 'p21-direct-git-archive-parts/v1'
            and manifest['part_count'] == PART_COUNT and manifest['plan_sha256'] == PLAN_BINDING[1]
            and manifest['producer_sha256'] == HELPER_SHA, 'Manifest provenance differs')
    require((manifest['full_archive']['bytes'], manifest['full_archive']['sha256']) == WHOLE, 'Manifest whole archive binding differs')
    parts = manifest['parts']
    validate_layout(parts, WHOLE)
    require(len(parts) == len(archive['parts']) == PART_COUNT, 'Archive part count differs')
    for index, (part, original) in enumerate(zip(parts, archive['parts'])):
        for key in ('index', 'offset', 'bytes', 'sha256', 'git_blob_sha'):
            require(part[key] == original[key], f'PLAN/manifest part {index} differs')
        path = BASE + f'/archive-parts/part-{index:05d}.bin'
        require(part['path'] == path and rows[path] == part['git_blob_sha'], f'Exact tree part {index} differs')
    return parts


def validate_auxiliary_metadata(plan, lossless, method, rows):
    for document in (lossless, method):
        require(document['plan_sha256'] == PLAN_BINDING[1] and document['producer_sha256'] == HELPER_SHA
                and document['source_snapshot_commit'] == SOURCE_SNAPSHOT and document['base_commit'] == PARENT
                and document['accepted_git_commit'] == ACCEPTED and document['accepted_git_tree'] == ACCEPTED_TREE,
                'Auxiliary metadata provenance differs')
        require(document['record_phase'] == 'prepared_before_push'
                and all(document[key] is False for key in ('local_archive_verified', 'compile_credit',
                                                          'kernel_credit', 'full_p2_complete')),
                'Prepared metadata credit boundary differs')
    require(lossless['schema'] == 'p21-lossless-original-assets/v1'
            and set(lossless['assets']) == set(plan['assets']) == set(ASSET_NAMES) | {'archive'},
            'Lossless asset set differs')
    require(method['schema'] == 'p21-direct-git-transport-method/v1'
            and method['prepared_archive_part_count'] == PART_COUNT
            and method['source_tree_check']['source_count'] == 140, 'Transport metadata scope differs')
    for name, asset in lossless['assets'].items():
        require(asset['original'] == plan['assets'][name], 'Lossless original PLAN descriptor differs: ' + name)
        if name == 'archive':
            require(asset['parts_manifest'] == MANIFEST_PATH, 'Archive parts manifest path differs')
            continue
        stored = asset['stored']
        path = BASE + '/original-assets/' + ASSET_NAMES[name]
        require(stored['path'] == path and rows[path] == stored['git_blob_sha']
                and stored['encoding'] == 'xz' and stored['preset'] == 6 and stored['check'] == 'CRC64',
                'Stored original format/path/tree differs: ' + name)
        require(type(stored['bytes']) is int and stored['bytes'] > 0
                and re.fullmatch('[0-9a-f]{64}', stored['sha256']) is not None
                and re.fullmatch('[0-9a-f]{40}', stored['git_blob_sha']) is not None,
                'Stored original digest descriptor differs: ' + name)
    return {name: lossless['assets'][name] for name in ASSET_NAMES}


def retrieve(work_root, output, helper, bare=None):
    run = Path(tempfile.mkdtemp(prefix='retrieve-', dir=work_root))
    report = {'schema': 'p21-authorized-git-retrieval/v1', 'run_directory': str(run),
              'implementation_origin': 'restored_from_saved_spec_original_temporary_source_not_recovered',
              'script_sha256': raw_sha(Path(__file__).read_bytes()), 'helper_sha256': HELPER_SHA,
              'remote': REMOTE, 'evidence_ref': EVIDENCE_REF, 'commit': COMMIT, 'tree': TREE,
              'accepted_git_commit': ACCEPTED, 'accepted_git_tree': ACCEPTED_TREE,
              'source_snapshot_commit': SOURCE_SNAPSHOT, 'original_declared_source_count': 140,
              'source_scope_note': 'Pinned metadata retains the original 140 selected sources; this program does not recompile Lean or independently rehash the source worktree.',
              'compile_credit': False, 'kernel_credit': False, 'full_p2_proved': False, 'full_p2_complete': False,
              'archive_bytes_verified': False, 'local_archive_verified': False,
              'original_archive_verification_passed': False, 'archive_verifier_executed': False,
              'remote_write_performed': False, 'synthetic_test_only': False,
              'raw_git_output_scope': 'Complete original stdout/stderr in this local run; no fabricated MCP captures. Binary batch stdout is not a second published archive. The durable archive payload is the exact 409 Git blobs in the pinned commit.'}
    git = None
    try:
        check_destination(output, WHOLE, helper)
        require(os.statvfs(work_root).f_bavail * os.statvfs(work_root).f_frsize >= WHOLE[0] * 3 + 33554432,
                'Insufficient free space for bare objects, archive and full original Git stdout')
        repository = run / 'repository.git' if bare is None else bare
        require(repository.is_absolute() and repository.parent.resolve(strict=True) == repository.parent
                and not os.path.lexists(repository), 'Bare repository must be a new canonical path')
        git = AuditedGit(repository, run / 'git-audit', helper)
        git.run(['init', '--bare', '--object-format=sha1', str(git.repository)], with_repository=False)
        git.run(['remote', 'add', 'origin', REMOTE])
        git.run(['config', '--local', 'remote.origin.promisor', 'true'])
        git.run(['config', '--local', 'remote.origin.partialclonefilter', 'blob:none'])
        before_refs = git.run(['for-each-ref', '--format=%(refname) %(objectname)'])
        before_head = git.run(['symbolic-ref', 'HEAD'])
        remote_ref = git.run(['ls-remote', '--refs', 'origin', EVIDENCE_REF])
        require(remote_ref == f'{COMMIT}\t{EVIDENCE_REF}\n'.encode(), 'Published evidence ref differs')
        git.fetch([COMMIT])
        require(git.run(['rev-parse', '--verify', COMMIT + '^{commit}']) == (COMMIT + '\n').encode(), 'Commit differs')
        require(git.run(['rev-parse', '--verify', COMMIT + '^{tree}']) == (TREE + '\n').encode(), 'Commit tree differs')
        commit_raw = git.run(['cat-file', 'commit', COMMIT])
        header = commit_raw.split(b'\n\n', 1)[0].splitlines()
        require([line for line in header if line.startswith(b'parent ')] == [('parent ' + PARENT).encode()], 'Prepared commit parent differs')
        rows = parse_tree(git.run(['ls-tree', '-r', '-z', '--full-tree', COMMIT, '--',
                                  BASE + '/archive-parts', BASE + '/original-assets', *METADATA_BINDINGS]))
        expected_paths = ({BASE + f'/archive-parts/part-{index:05d}.bin' for index in range(PART_COUNT)}
                          | set(METADATA_BINDINGS)
                          | {BASE + '/original-assets/' + name for name in ASSET_NAMES.values()})
        require(set(rows) == expected_paths
                and all(rows[path] == binding[2] for path, binding in METADATA_BINDINGS.items()),
                'Exact archive/metadata/original tree path set differs')
        git.fetch([binding[2] for binding in METADATA_BINDINGS.values()])
        metadata = {}
        report['metadata'] = {}
        for path, binding in METADATA_BINDINGS.items():
            raw = git.run(['cat-file', 'blob', binding[2]])
            require((len(raw), raw_sha(raw)) == binding[:2], 'Pinned metadata bytes differ: ' + path)
            saved = run / Path(path).name
            with saved.open('xb') as target:
                target.write(raw)
            metadata[path] = saved
            report['metadata'][path] = {'path': str(saved), 'bytes': len(raw), 'sha256': raw_sha(raw),
                                        'git_blob_sha': binding[2], 'exact_commit_tree_matched': True}
        plan = helper.load_plan(metadata[PLAN_PATH], PLAN_BINDING[1])
        manifest = json.loads(metadata[MANIFEST_PATH].read_bytes())
        parts = validate_metadata(plan, manifest, rows)
        lossless = json.loads(metadata[BASE + '/LOSSLESS_ASSETS.json'].read_bytes())
        method = json.loads(metadata[BASE + '/TRANSPORT_METHOD.json'].read_bytes())
        auxiliary = validate_auxiliary_metadata(plan, lossless, method, rows)
        git.fetch([asset['stored']['git_blob_sha'] for asset in auxiliary.values()])
        originals = run / 'original-assets'
        originals.mkdir()
        report['auxiliary_originals'] = {}
        for name, asset in auxiliary.items():
            stored = asset['stored']
            saved = git.run(['cat-file', 'blob', stored['git_blob_sha']], return_path=True)
            check_stored_blob(saved, stored, helper)
            original = asset['original']
            receipt = restore_original(saved, original['parts'], (original['bytes'], original['sha256']),
                                       originals / ASSET_NAMES[name].removesuffix('.xz'), helper)
            receipt['stored_blob'] = {**stored, 'local_raw_git_stdout_path': str(saved)}
            report['auxiliary_originals'][name] = receipt
        objects = list(dict.fromkeys(part['git_blob_sha'] for part in parts))
        git.fetch(objects)
        report['retrieval'] = assemble(git, parts, WHOLE, output, helper)
        require(git.run(['for-each-ref', '--format=%(refname) %(objectname)']) == before_refs, 'Fetch changed local refs')
        require(git.run(['symbolic-ref', 'HEAD']) == before_head, 'Fetch changed local HEAD')
        require(not (git.repository / 'FETCH_HEAD').exists(), 'Unexpected FETCH_HEAD write')
        require(helper.frozen_bytes(Path(helper.__file__), HELPER_SHA), 'Helper changed during run')
        report.update(status='VERIFIED_GIT_RETRIEVAL', archive_bytes_verified=True,
                      exact_part_count=len(parts), unique_requested_blobs=len(objects), refs_unchanged=True,
                      exact_metadata_count=len(metadata), verified_auxiliary_original_count=len(auxiliary),
                      verified_auxiliary_original_plan_parts=sum(len(asset['original']['parts']) for asset in auxiliary.values()))
    except BaseException as error:
        report.update(status='FAILED', error=f'{type(error).__name__}: {error}',
                      error_notes=getattr(error, '__notes__', []))
    finally:
        report['git_commands'] = [] if git is None else git.records
        result_path = run / 'RETRIEVAL_RESULT.json'
        with result_path.open('x') as target:
            json.dump(report, target, indent=2, sort_keys=True)
            target.write('\n')
    print(json.dumps({'status': report['status'], 'result': str(result_path),
                      'archive_bytes_verified': report['archive_bytes_verified'],
                      'local_archive_verified': report['local_archive_verified'], 'error': report.get('error')}))
    return 0 if report['status'] == 'VERIFIED_GIT_RETRIEVAL' else 1


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute-retrieval', action='store_true', required=True)
    parser.add_argument('--work-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--bare', type=Path, help='Optional new bare repository path; must not exist')
    parser.add_argument('--helper', type=Path, required=True)
    args = parser.parse_args(argv)
    require(args.work_root.is_absolute() and args.work_root.resolve(strict=True) == args.work_root, 'Work root must be an existing canonical directory')
    return retrieve(args.work_root, args.output, load_helper(args.helper), args.bare)


if __name__ == '__main__':
    sys.exit(main())
