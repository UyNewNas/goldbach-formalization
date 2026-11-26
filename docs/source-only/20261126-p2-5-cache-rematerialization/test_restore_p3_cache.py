#!/usr/bin/env python3
"""Storage-boundary tests. No Lean executable or cloud environment is used."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest

PATH = Path(__file__).with_name('restore_p3_cache.py')
spec = importlib.util.spec_from_file_location('recovery', PATH)
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)


class RecoveryBoundaries(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.data = b'original exact historical bytes\n'
        self.sha = hashlib.sha256(self.data).hexdigest()

    def file(self, name, data=None):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(self.data if data is None else data)
        return p

    def archive(self, entries):
        path = self.root / 'payload.tar'
        with tarfile.open(path, 'w') as tf:
            for name, data, symbolic in entries:
                item = tarfile.TarInfo(name)
                if symbolic:
                    item.type, item.linkname = tarfile.SYMTYPE, '/etc/passwd'
                    tf.addfile(item)
                else:
                    item.size = len(data)
                    tf.addfile(item, io.BytesIO(data))
        return path

    def test_existing_target_never_overwritten(self):
        source = self.file('source')
        target = self.file('target', b'different original file')
        with self.assertRaisesRegex(RuntimeError, 'never overwrite'):
            R.install_link(source, target, self.sha)
        self.assertEqual(target.read_bytes(), b'different original file')

    def test_identical_existing_target_is_only_validated(self):
        source, target = self.file('source'), self.file('target')
        before = target.stat()
        self.assertEqual(R.install_link(source, target, self.sha), 'already_exact')
        after = target.stat()
        self.assertEqual((before.st_ino, before.st_mtime_ns), (after.st_ino, after.st_mtime_ns))

    def test_symlink_parent_is_not_followed(self):
        source = self.file('source')
        real = self.root / 'real'
        real.mkdir()
        (self.root / 'alias').symlink_to(real, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'Symlink'):
            R.install_link(source, self.root/'alias'/'target', self.sha)
        self.assertFalse((real/'target').exists())

    def test_install_does_not_accept_wrong_source_sha(self):
        source = self.file('source', b'wrong bytes')
        target = self.root / 'newtarget'
        with self.assertRaises(RuntimeError):
            R.install_link(source, target, self.sha)
        self.assertFalse(target.exists())

    def test_archive_member_is_content_bound(self):
        archive = self.archive([(self.sha, b'wrong bytes', False)])
        r = R.Resolver({self.sha})
        r.archive(archive)
        self.assertNotIn(self.sha, r.blobs)
        self.assertEqual(len(r.rejected), 1)

    def test_selected_tar_symlink_is_refused(self):
        archive = self.archive([(self.sha, b'', True)])
        with self.assertRaisesRegex(RuntimeError, 'regular file'):
            R.Resolver({self.sha}).archive(archive)

    def test_duplicate_selected_tar_member_is_refused(self):
        archive = self.archive([(self.sha, self.data, False), (self.sha, self.data, False)])
        with self.assertRaisesRegex(RuntimeError, 'Duplicate'):
            R.Resolver({self.sha}).archive(archive)

    def test_pinned_archive_transport_and_safe_extraction(self):
        archive = self.archive([('objects/'+self.sha, self.data, False)])
        r = R.Resolver({self.sha})
        r.archive(archive, {'objects/'+self.sha:self.sha}, '0'*64)
        self.assertFalse(r.blobs)
        r.archive(archive, {'objects/'+self.sha:self.sha}, R.digest(archive))
        stored = r.store(self.sha, self.root/'store')
        self.assertEqual(stored.read_bytes(), self.data)
        self.assertFalse((self.root/'objects').exists())

    def test_topological_missing_order_and_cycle_guard(self):
        graph = {'A':{'project_imports':[]},'B':{'project_imports':['A']},'C':{'project_imports':['B']}}
        self.assertEqual(R.topological(graph, ['C','B']), ['B','C'])
        graph['A']['project_imports']=['C']
        with self.assertRaisesRegex(RuntimeError, 'Cyclic'):
            R.topological(graph, ['C'])

    def test_cli_plan_has_no_writes_or_lean_execution(self):
        cfg=json.loads(PATH.with_name('RECOVERY_SELECTION.json').read_text())
        repository=PATH.parents[3]
        for name in ['consumer_receipt','witness_manifest','object_inventory']:
            self.file(cfg[name]['path'],(repository/cfg[name]['path']).read_bytes())
        cfg['sources_by_sha256']={}
        cfg['cas_archives']=[]
        selected = self.file('selection.json', json.dumps(cfg).encode())
        before = sorted((str(p.relative_to(self.root)),p.stat().st_size) for p in self.root.rglob('*'))
        result = subprocess.run([sys.executable,'-B',str(PATH),'--plan','--skip-cas',
            '--repository',str(self.root),'--selection',str(selected),'--selection-sha',R.digest(selected),
            '--result-dir',str(self.root/'must-not-be-created')],capture_output=True,text=True)
        self.assertEqual(result.returncode,2,result.stderr)
        report=json.loads(result.stdout)
        self.assertEqual(report['lean_executions'],[])
        self.assertEqual(report['exact_available_unique_hashes'],0)
        after = sorted((str(p.relative_to(self.root)),p.stat().st_size) for p in self.root.rglob('*'))
        self.assertEqual(before,after)

    def test_exact_selection_contract_and_no_gate_removal(self):
        cfg=json.loads(PATH.with_name('RECOVERY_SELECTION.json').read_text())
        repository=PATH.parents[3]
        consumer=json.loads((repository/cfg['consumer_receipt']['path']).read_text())
        witnesses=json.loads((repository/cfg['witness_manifest']['path']).read_text())
        R.check_selection_contract(cfg,consumer,witnesses)
        cfg['requirements'].pop()
        with self.assertRaisesRegex(RuntimeError,'requirement set changed'):
            R.check_selection_contract(cfg,consumer,witnesses)

    def test_normal_scope_cannot_include_already_available_owner(self):
        cfg=json.loads(PATH.with_name('RECOVERY_SELECTION.json').read_text())
        repository=PATH.parents[3]
        consumer=json.loads((repository/cfg['consumer_receipt']['path']).read_text())
        witnesses=json.loads((repository/cfg['witness_manifest']['path']).read_text())
        cfg['allowed_normal_rebuild_modules'].append('ImbalancedChen.P2Saving16Cell00Decoded')
        with self.assertRaisesRegex(RuntimeError,'ten actually missing'):
            R.check_selection_contract(cfg,consumer,witnesses)

    def test_started_p3_scan_header_is_not_completion(self):
        inventory={'scan_scope_and_errors':[{'environment':'P3','files_scanned':307108}],
                   'scope':{}}
        self.assertFalse(R.p3_inventory_complete(inventory))
        inventory['scope']={'p3_41_scan_completed':True,'p3_scan_exit_code':1}
        self.assertFalse(R.p3_inventory_complete(inventory))
        inventory['scope']={'p3_41_scan_completed':False,'p3_scan_exit_code':0}
        self.assertFalse(R.p3_inventory_complete(inventory))
        inventory['scope']={'p3_41_scan_completed':True,'p3_scan_exit_code':0}
        self.assertTrue(R.p3_inventory_complete(inventory))


if __name__ == '__main__':
    unittest.main(verbosity=2)
