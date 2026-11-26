#!/usr/bin/env python3
"""Synthetic local storage regressions only; no cloud, GitHub or Lean calls."""
import base64
import copy
import hashlib
import importlib.util
import json
import lzma
import os
from pathlib import Path
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


def dump(path, value):
    path.write_bytes((json.dumps(value, ensure_ascii=False, separators=(',', ':')) + '\n').encode())


def envelope(suffix, arguments, body):
    return {'tool': 'mcp__codex_apps__cloud_compile_private_8e1da5a7_' + suffix,
            'arguments': arguments, 'result': {'content': [{'type': 'text', 'text': json.dumps(body)}],
                                              'structuredContent': None, 'isError': False}}


class ColdRetentionTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue((HERE / 'cold_retain_p21_evidence.py').is_file(), 'Cold retention wrapper is missing')
        self.m = module(HERE / 'cold_retain_p21_evidence.py', 'cold_retention_under_test')
        self.h = module(HELPER, 'original_transfer_under_test')
        self.temp = tempfile.TemporaryDirectory(prefix='p21-cold-synthetic-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.parts = self.root / 'parts'
        self.parts.mkdir()
        self.data = (bytes(range(256)) * 4688)[:1_200_017]
        def put(name, raw):
            p = self.root / name
            p.write_bytes(raw)
            return {'path': str(p), 'bytes': len(raw), 'sha256': self.h.sha(raw)}
        final = {'archive': put('archive.bin', self.data),
                 'export_manifest': put('manifest.json', b'{}'),
                 'joint_receipt_probe_log': [put('joint.json', b'{}'), put('Joint.lean', b'-- synthetic'),
                                             put('joint.log', b'')],
                 'verification': put('verification.json', b'{}'), 'git_commit': 'synthetic',
                 'source_snapshot_commit': 'synthetic', 'git_tree': 'synthetic'}
        info = put('FINALIZATION.json', json.dumps(final).encode())
        self.plan_path = self.root / 'PLAN.json'
        self.plan = self.h.make_plan(Path(info['path']), info['sha256'], info['bytes'], self.plan_path,
                                    synthetic_test_only=True)
        dump(self.plan_path, self.plan)
        self.plan_sha = self.h.sha(self.plan_path.read_bytes())
        self.captures = []
        for i, part in enumerate(self.plan['assets']['archive']['parts']):
            raw = self.data[part['offset']:part['offset'] + part['bytes']]
            request = self.h.job_request(self.plan, self.plan_sha, 'archive', i, 'synthetic-cold')
            job = f'{i + 1:032x}'
            pages = []
            for offset in range(0, len(raw), 65535):
                chunk = raw[offset:offset + 65535]
                body = {'output': chunk.decode('utf-8', errors='replace'),
                        'output_base64': base64.b64encode(chunk).decode(), 'stream': 'combined',
                        'next_offset': offset + len(chunk), 'eof': offset + len(chunk) == len(raw),
                        'log_truncated': False, 'discarded_bytes': 0}
                pages.append(envelope('read_task_output', {'task_id': job, 'offset': offset, 'limit': 65535}, body))
            state = {'job_id': job, 'task_id': job, 'cwd': request['cwd'], 'status': 'succeeded',
                     'exit_code': 0, 'log_bytes': len(raw), 'log_truncated': False, 'log_discarded_bytes': 0}
            capture = {'schema': 'p21-raw-task-capture/v1', 'synthetic_test_only': True,
                       'attempt': 'synthetic-cold', 'submission': envelope('run_command', request, {'job_id': job}),
                       'terminal': envelope('get_task', {'task_id': job}, state), 'pages': pages}
            self.captures.append(capture)
            self.save_part(i, raw, capture)
        self.store = self.m.ColdStore(HELPER, self.plan_path, self.plan_sha, self.parts, allow_synthetic=True)

    def paths(self, i):
        return self.parts / f'archive.{i:05}.bin', self.parts / f'archive.{i:05}.capture.json'

    def save_part(self, i, raw, capture):
        binary, calls = self.paths(i)
        binary.write_bytes(raw)
        dump(calls, capture)
        saved = calls.read_bytes()
        z = lzma.compress(saved, preset=6)
        blob = self.h.blob_sha(z)
        publication = {'index': i, 'asset': 'archive', 'bytes': len(z), 'sha256': self.h.sha(z),
                       'git_blob_sha': blob, 'remote_blob_sha': blob, 'github_blob_verified': True,
                       'raw_capture_bytes': len(saved), 'raw_capture_calls_sha256': self.h.sha(saved),
                       'path': f'docs/verification/20261126-p2-1/transport-captures/archive-{i:05}.json.xz',
                       'result': {'isError': False, 'structuredContent': {'sha': blob}, 'content': []}}
        dump(self.parts / f'archive.{i:05}.capture-publication.json', publication)
        part = self.plan['assets']['archive']['parts'][i]
        raw_publication = {'github_blob_verified': True, 'remote_blob_sha': part['git_blob_sha'],
                           'result': {'isError': False, 'structuredContent': {'sha': part['git_blob_sha']}, 'content': []}}
        dump(self.parts / f'archive.{i:05}.result.json', {'asset': 'archive', 'index': i, 'publication': raw_publication})

    def test_default_retain_preserves_hot_bytes_and_rejects_unverified_actual_git_sha(self):
        record = self.store.retain('archive', 0)
        binary, capture = self.paths(0)
        self.assertTrue(binary.is_file() and capture.is_file())
        self.assertEqual(lzma.decompress((self.parts / record['cold_capture']['path']).read_bytes()), capture.read_bytes())
        p = self.parts / 'archive.00001.capture-publication.json'
        value = json.loads(p.read_bytes())
        value['result']['structuredContent']['sha'] = '0' * 40
        dump(p, value)
        with self.assertRaises(ValueError):
            self.store.retain('archive', 1)
        self.assertTrue(all(p.is_file() for p in self.paths(1)))
        self.assertFalse((self.parts / 'archive.00001.cold-retention.json').exists())

    def test_cold_restore_runs_original_accept_and_assemble_one_pair_at_a_time(self):
        for i in range(2):
            self.store.retain('archive', i)
            self.store.evict('archive', i)
            self.assertFalse(any(p.exists() for p in self.paths(i)))
        observed = []
        original = self.store.helper.accept
        def inspect(*args, **kwargs):
            directory = args[4].parent
            self.assertEqual(len(list(directory.glob('*.bin'))), 1)
            self.assertEqual(len(list(directory.glob('*.capture.json'))), 1)
            observed.append(args[3])
            return original(*args, **kwargs)
        output = self.root / 'rebuilt.bin'
        with patch.object(self.store.helper, 'accept', side_effect=inspect):
            result = self.store.assemble('archive', output)
        self.assertEqual(output.read_bytes(), self.data)
        self.assertEqual(result['status'], 'SYNTHETIC_REASSEMBLED')
        self.assertEqual(observed, [0, 0, 1, 1])
        self.assertFalse(list(self.parts.glob('p21-cold-restore-*')))
        self.assertEqual(len(result['verified_parts']), 2)
        result = self.store.assemble('archive', output)
        self.assertEqual(result['status'], 'SYNTHETIC_REASSEMBLED')

    def test_corrupt_cold_bytes_are_rejected_even_if_full_output_already_exists(self):
        for i in range(2):
            self.store.retain('archive', i)
            self.store.evict('archive', i)
        output = self.root / 'existing.bin'
        output.write_bytes(self.data)
        record = json.loads((self.parts / 'archive.00001.cold-retention.json').read_bytes())
        cold = self.parts / record['cold_capture']['path']
        raw = cold.read_bytes()
        cold.write_bytes(raw[:-1] + bytes([raw[-1] ^ 1]))
        with self.assertRaises(ValueError):
            self.store.assemble('archive', output)
        self.assertEqual(output.read_bytes(), self.data)
        self.assertTrue(cold.exists())
        self.assertFalse(list(self.parts.glob('p21-cold-restore-*')))

    def test_original_capture_offset_gate_cannot_be_replaced_by_matching_hashes(self):
        bad = copy.deepcopy(self.captures[0])
        bad['pages'][1]['arguments']['offset'] += 1
        self.save_part(0, self.paths(0)[0].read_bytes(), bad)
        with self.assertRaises(ValueError):
            self.store.retain('archive', 0)
        self.assertFalse((self.parts / 'archive.00000.cold-retention.json').exists())

    def test_assembly_failure_cleans_owned_temporaries_and_preserves_cold(self):
        cold_hashes = {}
        for i in range(2):
            record = self.store.retain('archive', i)
            self.store.evict('archive', i)
            p = self.parts / record['cold_capture']['path']
            cold_hashes[p] = hashlib.sha256(p.read_bytes()).hexdigest()
        original = self.store.helper.accept
        def fail_second(*args, **kwargs):
            result = original(*args, **kwargs)
            if args[3] == 1:
                raise ValueError('synthetic interrupted original acceptance')
            return result
        output = self.root / 'failed.bin'
        with patch.object(self.store.helper, 'accept', side_effect=fail_second):
            with self.assertRaises(ValueError):
                self.store.assemble('archive', output)
        self.assertFalse(output.exists())
        self.assertFalse(list(self.root.glob('failed.bin.*.partial')))
        self.assertFalse(list(self.parts.glob('p21-cold-restore-*')))
        for p, sha in cold_hashes.items():
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(), sha)

    def test_production_mode_rejects_synthetic_and_modified_helper(self):
        store = self.m.ColdStore(HELPER, self.plan_path, self.plan_sha, self.parts)
        with self.assertRaises(ValueError):
            store.retain('archive', 0)
        other = self.root / 'changed_helper.py'
        other.write_bytes(HELPER.read_bytes() + b'\n')
        with self.assertRaises(ValueError):
            self.m.ColdStore(other, self.plan_path, self.plan_sha, self.parts, allow_synthetic=True)

    def test_evict_refuses_cold_bytes_changed_after_successful_restore(self):
        record = self.store.retain('archive', 0)
        cold = self.parts / record['cold_capture']['path']
        original = self.store.materialize
        def change_after_restore(*args, **kwargs):
            result = original(*args, **kwargs)
            cold.write_bytes(cold.read_bytes() + b'changed after acceptance')
            return result
        with patch.object(self.store, 'materialize', side_effect=change_after_restore):
            with self.assertRaises(ValueError):
                self.store.evict('archive', 0)
        self.assertTrue(all(p.is_file() for p in self.paths(0)))

    def test_cleanup_refuses_replaced_inode_and_preserves_foreign_file(self):
        area = self.m.RestoreArea(self.parts)
        original = area.put('owned.bin', b'owned')
        original.rename(area.path / 'moved-original.bin')
        original.write_bytes(b'foreign replacement')
        with self.assertRaises(ValueError):
            area.clear()
        self.assertEqual(original.read_bytes(), b'foreign replacement')
        self.assertEqual((area.path / 'moved-original.bin').read_bytes(), b'owned')

    def test_restore_owns_created_fd_even_if_path_replaced_before_registration(self):
        area = self.m.RestoreArea(self.parts)
        original_open = Path.open
        destination = area.path / 'new.bin'
        moved = area.path / 'moved-created.bin'
        def replace_after_open(path, *args, **kwargs):
            stream = original_open(path, *args, **kwargs)
            if path == destination and args == ('xb',):
                path.rename(moved)
                with original_open(path, 'wb') as replacement:
                    replacement.write(b'foreign replacement')
            return stream
        with patch.object(Path, 'open', replace_after_open):
            with self.assertRaises(ValueError):
                area.put('new.bin', b'owned data')
        with self.assertRaises(ValueError):
            area.clear()
        self.assertEqual(destination.read_bytes(), b'foreign replacement')
        self.assertTrue(moved.is_file())

    def test_atomic_write_refuses_path_replaced_before_ownership_registration(self):
        original_mkstemp = tempfile.mkstemp
        names = {}
        def replaced_temp(*args, **kwargs):
            fd, name = original_mkstemp(*args, **kwargs)
            temporary = Path(name)
            moved = temporary.with_name(temporary.name + '.moved')
            temporary.rename(moved)
            temporary.write_bytes(b'foreign replacement')
            names.update(temporary=temporary, moved=moved)
            return fd, name
        destination = self.parts / 'new-record.json'
        with patch.object(self.m.tempfile, 'mkstemp', replaced_temp):
            with self.assertRaises(ValueError):
                self.store.atomic_new(destination, b'owned data')
        self.assertFalse(destination.exists())
        self.assertEqual(names['temporary'].read_bytes(), b'foreign replacement')
        self.assertTrue(names['moved'].is_file())

    def test_retention_record_is_immutable_and_cold_symlink_is_rejected(self):
        record = self.store.retain('archive', 0)
        path = self.parts / 'archive.00000.cold-retention.json'
        original = path.read_bytes()
        self.store.retain('archive', 0)
        self.assertEqual(path.read_bytes(), original)
        path.write_bytes(original + b' ')
        with self.assertRaises(ValueError):
            self.store.retain('archive', 0)
        self.assertEqual(path.read_bytes(), original + b' ')
        path.write_bytes(original)
        cold = self.parts / record['cold_capture']['path']
        moved = cold.with_suffix('.original')
        cold.rename(moved)
        cold.symlink_to(moved)
        with self.assertRaises(ValueError):
            self.store.evict('archive', 0)
        self.assertTrue(all(p.is_file() for p in self.paths(0)))


if __name__ == '__main__':
    unittest.main(verbosity=2)
