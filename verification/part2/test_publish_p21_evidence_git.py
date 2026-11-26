#!/usr/bin/env python3
"""Local synthetic Git preparation regressions. No cloud calls or Git push."""
import base64
import hashlib
import importlib.util
import json
import lzma
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
HELPER = Path(os.environ.get('P21_TEST_ORIGINAL_HELPER', HERE / 'transfer_p21_evidence.py'))


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode()


def envelope(suffix, arguments, body):
    return {'tool': 'mcp__codex_apps__cloud_compile_private_8e1da5a7_' + suffix, 'arguments': arguments,
            'result': {'content': [{'type': 'text', 'text': json.dumps(body)}], 'isError': False}}


class DirectGitEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue((HERE / 'publish_p21_evidence_git.py').is_file(), 'Direct Git publisher is missing')
        self.m = module(HERE / 'publish_p21_evidence_git.py', 'publisher_under_test')
        self.h = module(HELPER, 'original_transfer_under_test')
        self.temporary = tempfile.TemporaryDirectory(prefix='p21-direct-git-synthetic-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.work = self.root / 'jobs'
        self.work.mkdir()
        self.origin = self.root / 'origin.git'
        self.env = {**os.environ, 'GIT_AUTHOR_NAME': 'Synthetic test fixture',
                    'GIT_AUTHOR_EMAIL': 'fixture@example.invalid', 'GIT_COMMITTER_NAME': 'Synthetic test fixture',
                    'GIT_COMMITTER_EMAIL': 'fixture@example.invalid', 'GIT_CONFIG_NOSYSTEM': '1',
                    'GIT_CONFIG_GLOBAL': '/dev/null'}
        self.fixture_git(['init', '--bare', str(self.origin)])
        self.fixture_git(['config', 'uploadpack.allowFilter', 'true'])
        self.source_path = 'ImbalancedChen/SyntheticFixture.lean'
        self.source = b'-- synthetic storage fixture; no Lean run\n'
        self.targets = {'source_snapshot_commit': 'a' * 40, 'project_module_count': 1,
                        'modules': [{'module': 'ImbalancedChen.SyntheticFixture', 'source': self.source_path,
                                     'source_sha256': self.h.sha(self.source)}]}
        targets_raw = encoded(self.targets)
        base_files = {self.source_path: self.source, self.m.TARGETS_PATH: targets_raw,
                      self.m.PUBLISHER_PATH: (HERE / 'publish_p21_evidence_git.py').read_bytes()}
        self.accepted = self.fixture_commit(base_files)
        accepted_tree = self.fixture_git(['rev-parse', self.accepted + '^{tree}']).decode().strip()
        self.data = (bytes(range(256)) * 4688)[:1_200_017]
        def source(name, raw):
            path = self.root / name
            path.write_bytes(raw)
            return {'path': str(path), 'bytes': len(raw), 'sha256': self.h.sha(raw)}
        final = {'archive': source('archive.bin', self.data),
                 'export_manifest': source('manifest.json', b'{"fixture":"manifest"}\n'),
                 'joint_receipt_probe_log': [source('receipt.json', b'{"fixture":"receipt"}\n'),
                                             source('Joint.lean', b'-- synthetic probe\n'), source('joint.log', b'synthetic log\n')],
                 'verification': source('verification.json', b'{"fixture":"verification"}\n'),
                 'git_commit': self.accepted, 'git_tree': accepted_tree,
                 'source_snapshot_commit': self.targets['source_snapshot_commit'], 'full_p2_complete': False,
                 'inputs': [{'path': str(self.root / self.m.TARGETS_PATH), 'bytes': len(targets_raw),
                             'sha256': self.h.sha(targets_raw)}]}
        final_info = source('FINALIZATION.json', encoded(final))
        self.plan_path = self.root / 'PLAN.json'
        self.plan = self.h.make_plan(Path(final_info['path']), final_info['sha256'], final_info['bytes'],
                                    self.plan_path, synthetic_test_only=True)
        self.save_plan()
        capture = self.capture(0)
        first = self.plan['assets']['archive']['parts'][0]
        base_files[self.m.PREFIX + '/archive-parts/part-00000.bin'] = self.data[:first['bytes']]
        base_files[self.m.PREFIX + '/transport-captures/archive-00000.json.xz'] = lzma.compress(encoded(capture), preset=6)
        self.base = self.fixture_commit(base_files, self.accepted)
        self.fixture_git(['update-ref', 'refs/heads/source', self.base])

    def fixture_git(self, args, data=None):
        self.assertNotIn('push', args, 'A test must never execute Git push')
        command = ['git']
        if self.origin.exists():
            command += ['--git-dir', str(self.origin)]
        result = subprocess.run(command + args, input=data, capture_output=True, env=self.env, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors='replace'))
        return result.stdout

    def fixture_commit(self, files, parent=None):
        self.fixture_git(['read-tree', '--empty'])
        lines = []
        for path, raw in sorted(files.items()):
            blob = self.fixture_git(['hash-object', '-w', '--stdin'], raw).decode().strip()
            lines.append(f'100644 {blob}\t{path}\0'.encode())
        self.fixture_git(['update-index', '-z', '--index-info'], b''.join(lines))
        tree = self.fixture_git(['write-tree']).decode().strip()
        args = ['commit-tree', tree] + (['-p', parent] if parent else [])
        return self.fixture_git(args, b'Synthetic local fixture\n').decode().strip()

    def save_plan(self):
        self.plan_path.write_bytes(encoded(self.plan))
        self.plan_sha = self.h.sha(self.plan_path.read_bytes())

    def capture(self, index):
        piece = self.plan['assets']['archive']['parts'][index]
        data = self.data[piece['offset']:piece['offset'] + piece['bytes']]
        job = f'{index + 1:032x}'
        request = self.h.job_request(self.plan, self.plan_sha, 'archive', index, 'synthetic-direct')
        state = {'job_id': job, 'task_id': job, 'cwd': request['cwd'], 'status': 'succeeded', 'exit_code': 0,
                 'log_bytes': len(data), 'log_truncated': False, 'log_discarded_bytes': 0}
        pages = []
        for offset in range(0, len(data), 65535):
            chunk = data[offset:offset + 65535]
            body = {'output': chunk.decode(errors='replace'), 'output_base64': base64.b64encode(chunk).decode(),
                    'stream': 'combined', 'next_offset': offset + len(chunk), 'eof': offset + len(chunk) == len(data),
                    'log_truncated': False, 'discarded_bytes': 0}
            pages.append(envelope('read_task_output', {'task_id': job, 'offset': offset, 'limit': 65535}, body))
        return {'schema': 'p21-raw-task-capture/v1', 'synthetic_test_only': True, 'attempt': 'synthetic-direct',
                'submission': envelope('run_command', request, {'job_id': job}),
                'terminal': envelope('get_task', {'task_id': job}, state), 'pages': pages}

    def publisher(self, **overrides):
        arguments = dict(helper=HELPER, plan=self.plan_path, plan_sha=self.plan_sha, source_branch='source',
                         expected_base=self.base, work_parent=self.work, repository=self.origin.as_uri(),
                         allow_synthetic=True)
        arguments.update(overrides)
        publisher = self.m.Publisher(**arguments)
        actual_git = publisher.git
        def never_push(args, *other, **kwargs):
            self.assertNotIn('push', args, 'A test must never execute Git push')
            self.assertNotIn('commit.gpgSign=false', args, 'Normal signing configuration must not be disabled')
            return actual_git(args, *other, **kwargs)
        publisher.git = never_push
        return publisher

    def test_prepare_preserves_base_and_verifies_every_original_without_push(self):
        publisher = self.publisher()
        result = publisher.run()
        self.assertEqual(result['status'], 'PREPARED_ONLY')
        self.assertFalse(result['push_performed'])
        self.assertFalse(result['full_p2_complete'])
        self.assertEqual(result['base_mcp_captures_verified'], 1)
        self.assertEqual(result['archive_part_count'], 2)
        tree = publisher.tree_entries(result['evidence_commit'])
        base = publisher.tree_entries(self.base)
        self.assertTrue(all(tree[path] == entry for path, entry in base.items()))
        self.assertTrue(all(path.startswith(self.m.PREFIX + '/') for path in tree.keys() - base.keys()))
        rebuilt = b''.join(publisher.git(['cat-file', 'blob', tree[f'{self.m.PREFIX}/archive-parts/part-{i:05}.bin'][2]]).stdout
                           for i in range(2))
        self.assertEqual(rebuilt, self.data)
        parts = json.loads(publisher.git(['show', result['evidence_commit'] + ':' + self.m.PREFIX + '/ARCHIVE_PARTS.json']).stdout)
        self.assertEqual(parts['full_archive'], {'bytes': len(self.data), 'sha256': self.h.sha(self.data)})
        assets = json.loads(publisher.git(['show', result['evidence_commit'] + ':' + self.m.PREFIX + '/LOSSLESS_ASSETS.json']).stdout)
        for name, row in assets['assets'].items():
            if name == 'archive':
                continue
            compressed = publisher.git(['show', result['evidence_commit'] + ':' + row['stored']['path']]).stdout
            self.assertEqual(lzma.decompress(compressed), Path(self.plan['assets'][name]['path']).read_bytes())
        method = json.loads(publisher.git(['show', result['evidence_commit'] + ':' + self.m.PREFIX + '/TRANSPORT_METHOD.json']).stdout)
        self.assertEqual(method['record_phase'], 'prepared_before_push')
        self.assertEqual(method['archive_direct_git_indices'], [1])
        self.assertFalse(method['local_archive_verified'])
        self.assertEqual(method['new_mcp_jobs'], 0)
        self.assertIn('other completed captures may be appended by root', method['mcp_scope_note'])

    def test_wrong_plan_and_part_sha_are_rejected(self):
        with self.assertRaises(ValueError):
            self.publisher(plan_sha='0' * 64)
        self.plan['assets']['archive']['parts'][1]['sha256'] = '0' * 64
        self.save_plan()
        publisher = self.publisher()
        with self.assertRaises(ValueError):
            publisher.run()
        self.assertIsNone(publisher.bare)

    def test_changed_source_during_object_writing_is_rejected(self):
        publisher = self.publisher()
        original = publisher.write_blob
        def change_first_byte(path, data, expected=None):
            result = original(path, data, expected)
            if path.endswith('/part-00000.bin'):
                with Path(self.plan['assets']['archive']['path']).open('r+b') as stream:
                    stream.write(b'changed')
            return result
        with patch.object(publisher, 'write_blob', side_effect=change_first_byte):
            with self.assertRaises(ValueError):
                publisher.run()
        self.assertFalse(publisher.report['push_performed'])

    def test_wrong_head_is_rejected(self):
        publisher = self.publisher(expected_base='0' * 40)
        with self.assertRaisesRegex(ValueError, 'Base HEAD differs'):
            publisher.run()

    def test_existing_evidence_ref_is_rejected_before_clone(self):
        self.fixture_git(['update-ref', self.m.EVIDENCE_REF, self.base])
        publisher = self.publisher()
        with self.assertRaisesRegex(ValueError, 'Evidence ref already exists'):
            publisher.run()
        self.assertIsNone(publisher.bare)

    def test_source_tree_delta_from_accepted_commit_is_rejected(self):
        files = {self.source_path: b'-- changed source\n', self.m.TARGETS_PATH: encoded(self.targets),
                 self.m.PUBLISHER_PATH: (HERE / 'publish_p21_evidence_git.py').read_bytes()}
        changed = self.fixture_commit(files, self.accepted)
        self.fixture_git(['update-ref', 'refs/heads/source', changed])
        publisher = self.publisher(expected_base=changed)
        with self.assertRaisesRegex(ValueError, 'Accepted source Git blob differs'):
            publisher.run()

    def test_git_trace_variables_are_removed_not_zeroed(self):
        with patch.dict(os.environ, {'GIT_TRACE': '1', 'GIT_TRACE_PACKET': '1', 'GIT_TRACE2_EVENT': 'trace-file',
                                     'GIT_CURL_VERBOSE': '1', 'GIT_CONFIG_COUNT': '0'}):
            env = self.m.git_environment()
        self.assertFalse(any(key.startswith('GIT_TRACE') or key == 'GIT_CURL_VERBOSE' for key in env))
        self.assertEqual(env['GIT_CONFIG_COUNT'], '0')

    def test_production_git_command_does_not_override_normal_hooks(self):
        publisher = self.publisher()
        original_run = subprocess.run
        with patch.object(self.m.subprocess, 'run', wraps=original_run) as observed:
            publisher.git(['--version'], inside=False)
        command = observed.call_args.args[0]
        self.assertFalse(any('core.hooksPath' in argument for argument in command))
        self.assertIn('pack.window=0', command)
        self.assertIn('pack.depth=0', command)
        self.assertIn('pack.threads=1', command)


if __name__ == '__main__':
    unittest.main(verbosity=2)
