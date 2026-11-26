#!/usr/bin/env python3
"""Prepare frozen P2.1 evidence in a fresh bare Git repository.

Default: prepare only. --push creates only the fixed, previously absent evidence
ref with an expected-empty lease and then verifies its remote SHA. No Lean run,
credential inspection, source-worktree edit or automatic repository cleanup.
"""
import argparse
import hashlib
import json
import lzma
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
import types

HELPER_SHA = '5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d'
PLAN_SHA = 'ac1d24aaf71dbc1f5cf89f8ab205f25fd58d8689726c81337a2499666bae068b'
REPOSITORY = 'https://github.com/UyNewNas/goldbach-formalization.git'
EVIDENCE_REF = 'refs/heads/evidence/p2-1-20261126-6c7864ad'
PREFIX = 'docs/verification/20261126-p2-1'
TARGETS_PATH = 'docs/verification/20261125-p2-1/TARGETS.json'
PUBLISHER_PATH = 'verification/part2/publish_p21_evidence_git.py'
AUTHOR_NAME = 'P2 evidence exporter'
AUTHOR_EMAIL = 'p2-evidence-exporter@example.invalid'
ASSET_NAMES = {'export_manifest': 'export-manifest.json.xz', 'joint_receipt': 'joint-receipt.json.xz',
               'joint_log': 'joint.log.xz', 'joint_probe': 'Joint.lean.xz', 'finalization': 'FINALIZATION.json.xz',
               'verification': 'verification.json.xz', 'retention': 'PERSISTENT_COPY.json.xz'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode()


def git_environment():
    routing = {'GIT_DIR', 'GIT_WORK_TREE', 'GIT_COMMON_DIR', 'GIT_INDEX_FILE', 'GIT_OBJECT_DIRECTORY',
               'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_NAMESPACE', 'GIT_PREFIX'}
    env = {key: value for key, value in os.environ.items()
           if not key.startswith('GIT_TRACE') and key != 'GIT_CURL_VERBOSE' and key not in routing}
    env.update(GIT_TERMINAL_PROMPT='0', GIT_AUTHOR_NAME=AUTHOR_NAME, GIT_AUTHOR_EMAIL=AUTHOR_EMAIL,
               GIT_COMMITTER_NAME=AUTHOR_NAME, GIT_COMMITTER_EMAIL=AUTHOR_EMAIL)
    return env


def load_original(path):
    require(path.is_absolute() and path.resolve(strict=True) == path
            and stat.S_ISREG(path.lstat().st_mode), 'Original helper is not canonical regular')
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == HELPER_SHA, 'Original helper SHA differs')
    helper = types.ModuleType('p21_original_transfer_for_git')
    helper.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), helper.__dict__)
    helper.frozen_bytes(path, HELPER_SHA, len(raw))
    return helper


class Publisher:
    def __init__(self, *, helper, plan, plan_sha, source_branch, expected_base, work_parent,
                 repository=REPOSITORY, allow_synthetic=False):
        self.helper_path, self.plan_path, self.plan_sha = helper, plan, plan_sha
        self.h = load_original(helper)
        self.plan = self.h.load_plan(plan, plan_sha)
        require(allow_synthetic or (repository == REPOSITORY and plan_sha == PLAN_SHA
                                   and self.plan['synthetic_test_only'] is False), 'Production plan/repository differs')
        require(not allow_synthetic or (self.plan['synthetic_test_only'] is True and repository.startswith('file://')),
                'Synthetic regressions require a local file repository and synthetic plan')
        require(re.fullmatch('[0-9a-f]{40}', expected_base), 'Expected base must be a full commit SHA')
        require(re.fullmatch('[A-Za-z0-9][A-Za-z0-9._/-]*', source_branch), 'Invalid source branch')
        require(work_parent.is_absolute() and work_parent.resolve(strict=True) == work_parent and work_parent.is_dir(),
                'Work parent is not canonical')
        self.source_branch, self.expected_base = source_branch, expected_base
        self.repository, self.allow_synthetic, self.work_parent = repository, allow_synthetic, work_parent
        self.bare = self.work_directory = self.report_path = None
        self.base_entries, self.written, self.mcp_captures, self.git_calls = {}, {}, [], []
        self.runtime_path = Path(__file__).resolve()
        stream, before = self.h.regular(self.runtime_path)
        with stream:
            self.runtime_bytes = stream.read()
            self.h.unchanged(self.runtime_path, stream, before)
        self.report = {'schema': 'p21-direct-git-run/v1', 'status': 'NOT_PREPARED',
                       'plan_sha256': plan_sha, 'producer_sha256': HELPER_SHA,
                       'publisher_sha256': self.h.sha(self.runtime_bytes), 'expected_base': expected_base,
                       'evidence_ref': EVIDENCE_REF, 'source_snapshot_commit': self.plan['source_snapshot_commit'],
                       'accepted_git_commit': self.plan['git_commit'], 'accepted_git_tree': self.plan['git_tree'],
                       'synthetic_test_only': self.plan['synthetic_test_only'], 'push_attempted': False,
                       'push_performed': False, 'remote_verified': False, 'local_archive_verified': False,
                       'compile_credit': False, 'kernel_credit': False, 'full_p2_complete': False}

    def git(self, args, data=None, *, inside=True, record=False, check=True):
        command = ['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false',
                   '-c', 'pack.window=0', '-c', 'pack.depth=0', '-c', 'pack.threads=1']
        env = git_environment()
        if inside:
            require(self.bare is not None, 'Bare repository not initialized')
            command += ['--git-dir', str(self.bare)]
            env['GIT_INDEX_FILE'] = str(self.bare / 'p21-evidence.index')
        result = subprocess.run(command + args, input=data, capture_output=True, env=env,
                                cwd=self.work_parent, timeout=3000)
        if record or result.returncode:
            self.git_calls.append({'arguments': args, 'returncode': result.returncode,
                                   'stdout': result.stdout.decode('utf-8', errors='replace'),
                                   'stderr': result.stderr.decode('utf-8', errors='replace')})
        require(not check or result.returncode == 0, f'Git {args[0]} failed with returncode {result.returncode}')
        return result

    def remote_ref(self):
        result = self.git(['ls-remote', '--refs', self.repository, EVIDENCE_REF], inside=False, record=True)
        lines = result.stdout.decode('ascii').splitlines()
        require(len(lines) <= 1, 'Remote returned multiple evidence refs')
        if not lines:
            return None
        fields = lines[0].split()
        require(len(fields) == 2 and fields[1] == EVIDENCE_REF and re.fullmatch('[0-9a-f]{40}', fields[0]),
                'Unexpected remote ref response')
        return fields[0]

    def freeze_sources(self):
        for name, entry in self.plan['assets'].items():
            require(self.h.freeze(entry) == entry, 'Original frozen asset/parts/stamp differs: ' + name)

    def sources_unchanged(self):
        self.h.frozen_bytes(self.plan_path, self.plan_sha)
        self.h.frozen_bytes(self.helper_path, HELPER_SHA)
        self.h.frozen_bytes(self.runtime_path, self.h.sha(self.runtime_bytes), len(self.runtime_bytes))
        for name, entry in self.plan['assets'].items():
            path = Path(entry['path'])
            stream, before = self.h.regular(path)
            with stream:
                require(before == entry['stamp'], 'Frozen source stamp changed: ' + name)
                self.h.unchanged(path, stream, before)

    def tree_entries(self, revision):
        raw = self.git(['ls-tree', '-r', '-z', '--full-tree', revision]).stdout
        result = {}
        for row in raw.split(b'\0'):
            if not row:
                continue
            header, path = row.split(b'\t', 1)
            mode, kind, oid = header.decode('ascii').split()
            name = path.decode('utf-8', errors='surrogateescape')
            require(name not in result, 'Duplicate Git tree path')
            result[name] = (mode, kind, oid)
        return result

    def asset_chunks(self, name):
        entry = self.plan['assets'][name]
        path = Path(entry['path'])
        stream, before = self.h.regular(path)
        digest, count = hashlib.sha256(), 0
        with stream:
            require(before == entry['stamp'], 'Frozen source stamp changed: ' + name)
            for piece in entry['parts']:
                raw = stream.read(piece['bytes'])
                require(len(raw) == piece['bytes'] and self.h.sha(raw) == piece['sha256']
                        and self.h.blob_sha(raw) == piece['git_blob_sha'], 'Original part hash differs: ' + name)
                digest.update(raw)
                count += len(raw)
                yield piece, raw
            require(stream.read(1) == b'', 'Original source has trailing bytes')
            self.h.unchanged(path, stream, before)
        require(count == entry['bytes'] and digest.hexdigest() == entry['sha256'], 'Original asset hash differs: ' + name)

    def verify_source_tree(self):
        accepted = self.plan['git_commit']
        self.git(['fetch', '--no-tags', '--filter=blob:none', '--depth=1', 'origin', accepted], record=True)
        require(self.git(['rev-parse', accepted + '^{tree}']).stdout.decode().strip() == self.plan['git_tree'],
                'Accepted Git tree differs from original plan')
        accepted_entries = self.tree_entries(accepted)
        require(self.base_entries.get(TARGETS_PATH) == accepted_entries.get(TARGETS_PATH)
                and TARGETS_PATH in accepted_entries, 'Frozen target manifest differs in base')
        targets_blob = accepted_entries[TARGETS_PATH][2]
        targets_raw = self.git(['cat-file', 'blob', targets_blob]).stdout
        final = json.loads(b''.join(raw for _, raw in self.asset_chunks('finalization')))
        target_infos = [info for info in final['inputs'] if info['path'].endswith('/' + TARGETS_PATH)]
        require(len(target_infos) == 1 and self.h.sha(targets_raw) == target_infos[0]['sha256']
                and len(targets_raw) == target_infos[0]['bytes'], 'Original FINALIZATION target binding differs')
        targets = json.loads(targets_raw)
        modules = targets['modules']
        require(targets['source_snapshot_commit'] == self.plan['source_snapshot_commit']
                and len(modules) == targets['project_module_count']
                and len({row['source'] for row in modules}) == len(modules)
                and (self.allow_synthetic or len(modules) == 140), 'Frozen target source scope differs')
        rows = []
        for row in modules:
            path = row['source']
            require(path.startswith('ImbalancedChen/') and '..' not in PurePosixPath(path).parts,
                    'Unexpected target source path')
            original = accepted_entries.get(path)
            require(original is not None and original[0:2] == ('100644', 'blob')
                    and self.base_entries.get(path) == original, 'Accepted source Git blob differs: ' + path)
            rows.append({'module': row['module'], 'path': path, 'git_blob_sha': original[2],
                         'target_source_sha256': row['source_sha256']})
        require(self.base_entries.get(PUBLISHER_PATH) == ('100644', 'blob', self.h.blob_sha(self.runtime_bytes)),
                'Running publisher bytes do not match expected base')
        return {'accepted_commit': accepted, 'accepted_tree': self.plan['git_tree'], 'base_commit': self.expected_base,
                'targets_blob_sha': targets_blob, 'targets_sha256': self.h.sha(targets_raw),
                'source_count': len(rows), 'sources': rows}

    def write_blob(self, path, data, expected=None):
        require(path.startswith(PREFIX + '/') and '..' not in PurePosixPath(path).parts
                and not any(c in path for c in '\n\r\t\0'), 'Output path is outside evidence scope')
        calculated = self.h.blob_sha(data)
        require(expected is None or calculated == expected, 'Prepared Git blob differs from plan')
        oid = self.git(['hash-object', '-w', '--stdin'], data).stdout.decode('ascii').strip()
        require(oid == calculated and (expected is None or oid == expected), 'Actual git hash-object differs')
        entry = ('100644', 'blob', oid)
        require(path not in self.base_entries or self.base_entries[path] == entry,
                'Refusing to replace existing evidence bytes: ' + path)
        require(path not in self.written or self.written[path] == entry, 'Duplicate differing prepared path')
        self.written[path] = entry
        return oid

    def verify_base_capture(self, asset, index, raw):
        path = f'{PREFIX}/transport-captures/{asset}-{index:05}.json.xz'
        entry = self.base_entries.get(path)
        if entry is None:
            return None
        require(entry[:2] == ('100644', 'blob'), 'Existing capture is not a regular Git blob')
        if asset == 'archive':
            part_path = f'{PREFIX}/archive-parts/part-{index:05}.bin'
            require(self.base_entries.get(part_path) == ('100644', 'blob', self.h.blob_sha(raw)),
                    'Existing archive capture lacks its matching published raw part')
        compressed = self.git(['cat-file', 'blob', entry[2]]).stdout
        require(self.h.blob_sha(compressed) == entry[2], 'Existing capture Git bytes differ')
        decoder = lzma.LZMADecompressor(memlimit=256 * 1024 * 1024)
        saved = decoder.decompress(compressed, max_length=32 * 1024 * 1024)
        require(decoder.eof and not decoder.unused_data, 'Existing raw capture exceeds the bounded original envelope')
        capture = json.loads(saved)
        job = self.h.validate_capture(self.plan, self.plan_sha, asset, index, raw, capture,
                                      allow_synthetic=self.allow_synthetic)
        row = {'asset': asset, 'index': index, 'job_id': job, 'capture_path': path,
               'capture_xz_git_blob_sha': entry[2], 'raw_capture_calls_sha256': self.h.sha(saved)}
        self.mcp_captures.append(row)
        return row

    def prepare(self):
        self.git(['check-ref-format', 'refs/heads/' + self.source_branch], inside=False)
        self.freeze_sources()
        require(self.remote_ref() is None, 'Evidence ref already exists; refusing creation')
        self.work_directory = Path(tempfile.mkdtemp(prefix='p21-direct-evidence-', dir=self.work_parent))
        owned = self.work_directory.lstat()
        self.report_path = self.work_directory.with_name(self.work_directory.name + '.json')
        self.report.update(work_directory=str(self.work_directory), report_path=str(self.report_path),
                           owned_work_directory={'st_dev': owned.st_dev, 'st_ino': owned.st_ino})
        self.bare = self.work_directory / 'repository.git'
        self.git(['clone', '--bare', '--filter=blob:none', '--depth=1', '--single-branch', '--no-tags',
                  '--branch', self.source_branch, self.repository, str(self.bare)], inside=False, record=True)
        self.report['bare_directory'] = str(self.bare)
        self.git(['config', 'gc.auto', '0'])
        self.git(['config', 'maintenance.auto', 'false'])
        require(self.git(['rev-parse', 'HEAD']).stdout.decode().strip() == self.expected_base, 'Base HEAD differs')
        self.base_entries = self.tree_entries(self.expected_base)
        source_check = self.verify_source_tree()
        archive_rows, assets = [], {}
        for name, original in self.plan['assets'].items():
            if name == 'archive':
                for piece, raw in self.asset_chunks(name):
                    path = f'{PREFIX}/archive-parts/part-{piece["index"]:05}.bin'
                    self.write_blob(path, raw, piece['git_blob_sha'])
                    capture = self.verify_base_capture(name, piece['index'], raw)
                    row = {**piece, 'path': path, 'transport': 'existing_base_mcp_capture' if capture else 'direct_git'}
                    if capture:
                        row['base_capture'] = capture
                    archive_rows.append(row)
                assets[name] = {'original': original, 'parts_manifest': PREFIX + '/ARCHIVE_PARTS.json'}
            else:
                require(name in ASSET_NAMES, 'Unknown original auxiliary asset')
                compressor = lzma.LZMACompressor(format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64, preset=6)
                compressed = bytearray()
                for piece, raw in self.asset_chunks(name):
                    compressed.extend(compressor.compress(raw))
                    self.verify_base_capture(name, piece['index'], raw)
                compressed.extend(compressor.flush())
                compressed = bytes(compressed)
                restored = lzma.decompress(compressed)
                require(len(restored) == original['bytes'] and self.h.sha(restored) == original['sha256'],
                        'Compressed auxiliary original differs')
                path = PREFIX + '/original-assets/' + ASSET_NAMES[name]
                oid = self.write_blob(path, compressed)
                assets[name] = {'original': original, 'stored': {'path': path, 'bytes': len(compressed),
                                                                 'sha256': self.h.sha(compressed), 'git_blob_sha': oid,
                                                                 'encoding': 'xz', 'preset': 6, 'check': 'CRC64'}}
        provenance = {'plan_sha256': self.plan_sha, 'producer_sha256': HELPER_SHA,
                      'source_snapshot_commit': self.plan['source_snapshot_commit'],
                      'accepted_git_commit': self.plan['git_commit'], 'accepted_git_tree': self.plan['git_tree'],
                      'base_commit': self.expected_base, 'record_phase': 'prepared_before_push',
                      'local_archive_verified': False, 'compile_credit': False, 'kernel_credit': False,
                      'full_p2_complete': False}
        archive = self.plan['assets']['archive']
        parts_manifest = {'schema': 'p21-direct-git-archive-parts/v1', **provenance,
                          'bytes': archive['bytes'], 'sha256': archive['sha256'], 'part_bytes': self.plan['part_bytes'],
                          'full_archive': {'bytes': archive['bytes'], 'sha256': archive['sha256']},
                          'part_count': len(archive_rows), 'parts': archive_rows}
        lossless = {'schema': 'p21-lossless-original-assets/v1', **provenance, 'assets': assets}
        base_archive_captures = [row for row in self.mcp_captures if row['asset'] == 'archive']
        method = {'schema': 'p21-direct-git-transport-method/v1', **provenance,
                  'method': 'standard authenticated Git; frozen source bytes written as verified Git objects',
                  'author': {'name': AUTHOR_NAME, 'email': AUTHOR_EMAIL}, 'new_mcp_jobs': 0,
                  'base_mcp_captures_verified': len(base_archive_captures),
                  'base_mcp_captures': self.mcp_captures,
                  'mcp_scope_note': 'Only captures in the pinned base were replayed here; other completed captures may be appended by root.',
                  'archive_direct_git_indices': [row['index'] for row in archive_rows if row['transport'] == 'direct_git'],
                  'prepared_archive_part_count': len(archive_rows), 'source_tree_check': source_check,
                  'publication_evidence': 'Actual push and remote readback belong to the separate post-operation run report.',
                  'remaining_gate': 'Download/reconstruct the full original archive and run the unchanged repack verifier locally.'}
        for name, value in [('ARCHIVE_PARTS.json', parts_manifest), ('LOSSLESS_ASSETS.json', lossless),
                            ('TRANSPORT_METHOD.json', method)]:
            self.write_blob(PREFIX + '/' + name, encoded(value))
        self.write_blob(PREFIX + '/DIRECT_GIT_PLAN.json', self.h.frozen_bytes(self.plan_path, self.plan_sha))
        self.sources_unchanged()
        self.git(['read-tree', self.expected_base])
        index_info = b''.join(f'{entry[0]} {entry[2]}\t{path}\0'.encode('utf-8')
                              for path, entry in sorted(self.written.items()))
        self.git(['update-index', '-z', '--index-info'], index_info)
        tree = self.git(['write-tree']).stdout.decode('ascii').strip()
        resulting_entries = self.tree_entries(tree)
        require(resulting_entries == {**self.base_entries, **self.written}, 'Prepared tree differs from exact additions')
        require(all(resulting_entries[path] == entry for path, entry in self.base_entries.items()),
                'Prepared tree modified a base entry')
        commit = self.git(['commit-tree', tree, '-p', self.expected_base],
                          b'Preserve frozen P2.1 evidence through direct Git transport\n\nNo new Lean or full P2 completion credit.\n').stdout.decode('ascii').strip()
        require(re.fullmatch('[0-9a-f]{40}', commit), 'Invalid prepared commit SHA')
        self.report.update(status='PREPARED_ONLY', evidence_commit=commit, evidence_tree=tree,
                           archive_part_count=len(archive_rows), archive_bytes=archive['bytes'], archive_sha256=archive['sha256'],
                           auxiliary_asset_count=len(assets) - 1, source_count=source_check['source_count'],
                           base_mcp_captures_verified=len(base_archive_captures),
                           new_file_count=len(resulting_entries) - len(self.base_entries))
        return commit

    def save_report(self):
        self.report['git_calls'] = self.git_calls
        if self.report_path is not None:
            raw = encoded(self.report)
            with self.report_path.open('xb') as stream:
                stream.write(raw)
                stream.flush()
                os.fsync(stream.fileno())
            self.h.frozen_bytes(self.report_path, self.h.sha(raw), len(raw))

    def run(self, push=False):
        try:
            commit = self.prepare()
            if push:
                require(not self.allow_synthetic, 'Synthetic tests cannot push')
                self.sources_unchanged()
                require(self.remote_ref() is None, 'Evidence ref already exists before push; refusing overwrite')
                self.report['push_attempted'] = True
                self.git(['push', '--porcelain', '--force-with-lease=' + EVIDENCE_REF + ':',
                          self.repository, commit + ':' + EVIDENCE_REF], record=True)
                self.report['push_performed'] = True
                remote = self.remote_ref()
                self.report['remote_ref_sha'] = remote
                require(remote == commit, 'Remote evidence ref does not equal the prepared commit')
                self.report.update(status='PUSHED_AND_REMOTE_VERIFIED', remote_verified=True)
            self.save_report()
            return self.report
        except Exception as error:
            self.report.update(status='FAILED_AFTER_PUSH' if self.report['push_performed'] else 'FAILED',
                               error=type(error).__name__ + ': ' + str(error))
            self.save_report()
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--helper', type=Path, required=True)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--plan-sha256', default=PLAN_SHA)
    parser.add_argument('--source-branch', required=True)
    parser.add_argument('--expected-base', required=True)
    parser.add_argument('--work-parent', type=Path, required=True)
    parser.add_argument('--push', action='store_true')
    args = parser.parse_args()
    publisher = None
    try:
        publisher = Publisher(helper=args.helper, plan=args.plan, plan_sha=args.plan_sha256,
                              source_branch=args.source_branch, expected_base=args.expected_base,
                              work_parent=args.work_parent)
        report = publisher.run(push=args.push)
        print(json.dumps(report, sort_keys=True, indent=2))
        return 0
    except Exception as error:
        report = publisher.report if publisher is not None else {'status': 'FAILED_BEFORE_PREPARATION',
                  'error': type(error).__name__ + ': ' + str(error), 'full_p2_complete': False}
        print(json.dumps(report, sort_keys=True, indent=2))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
