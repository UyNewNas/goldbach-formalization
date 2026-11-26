"""Small local-Git fixtures only. These are not production archive evidence."""
import copy
import errno
import hashlib
import importlib.util
import lzma
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).with_name('retrieve_git_archive_restored.py')
SPEC = importlib.util.spec_from_file_location('restored_retriever', SCRIPT)
R = importlib.util.module_from_spec(SPEC)
if SCRIPT.exists():
    SPEC.loader.exec_module(R)


class RetrievalRisks(unittest.TestCase):
    def setUp(self):
        self.assertTrue(hasattr(R, 'assemble'), 'Restoration assembly is not implemented')
        self.temp = tempfile.TemporaryDirectory(prefix='p21-retrieval-test-', dir='/dev/shm')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'objects.git'
        subprocess.run(['git', 'init', '--bare', '--object-format=sha1', str(self.repo)],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.helper = R.load_helper(SCRIPT.resolve().parents[2] / 'verification/part2/transfer_p21_evidence.py')
        self.git = R.AuditedGit(self.repo, self.root / 'audit', self.helper)
        self.data = [b'first local fixture\0\n', b'second local fixture\xff\n']
        self.parts = []
        offset = 0
        for index, raw in enumerate(self.data):
            oid = subprocess.run(['git', '-C', str(self.repo), 'hash-object', '-w', '--stdin'],
                                 input=raw, check=True, stdout=subprocess.PIPE).stdout.decode().strip()
            self.parts.append({'index': index, 'offset': offset, 'bytes': len(raw),
                               'sha256': hashlib.sha256(raw).hexdigest(), 'git_blob_sha': oid})
            offset += len(raw)
        self.expected = (offset, hashlib.sha256(b''.join(self.data)).hexdigest())
        self.output = self.root / 'archive.tar.xz'

    def run_assembly(self, parts=None):
        return R.assemble(self.git, self.parts if parts is None else parts,
                          self.expected, self.output, self.helper)

    def test_success_retains_exact_batch_stdout_and_rechecks_existing_output(self):
        result = self.run_assembly()
        self.assertEqual(self.output.read_bytes(), b''.join(self.data))
        self.assertEqual(result['status'], 'VERIFIED_REASSEMBLED_ORIGINAL')
        raw_batch = b''.join((p['git_blob_sha'] + ' blob ' + str(p['bytes']) + '\n').encode()
                             + raw + b'\n' for p, raw in zip(self.parts, self.data))
        record = self.git.records[-1]
        self.assertEqual(Path(record['stdout']['path']).read_bytes(), raw_batch)
        self.assertTrue(record['stdout_complete'])
        self.assertEqual(record['exit_code'], 0)
        inode = self.output.stat().st_ino
        reused = self.run_assembly()
        self.assertEqual(reused['status'], 'REUSED_WITH_VERIFIED_GIT_BYTES')
        self.assertEqual(self.output.stat().st_ino, inode)
        self.assertEqual(len(self.git.records), 2)

    def test_wrong_existing_output_is_preserved_without_git_read(self):
        self.output.write_bytes(b'wrong existing archive')
        before = self.output.stat()
        with self.assertRaisesRegex(ValueError, 'Existing output'):
            self.run_assembly()
        self.assertEqual(self.output.read_bytes(), b'wrong existing archive')
        self.assertEqual(self.output.stat().st_ino, before.st_ino)
        self.assertEqual(self.git.records, [])

    def test_gap_and_digest_corruption_fail_without_installing_partial(self):
        invalid = copy.deepcopy(self.parts)
        invalid[1]['offset'] += 1
        with self.assertRaisesRegex(ValueError, 'index/offset'):
            self.run_assembly(invalid)
        self.assertEqual(self.git.records, [])
        invalid = copy.deepcopy(self.parts)
        invalid[0]['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Part digest'):
            self.run_assembly(invalid)
        self.assertFalse(self.output.exists())
        self.assertEqual(list(self.root.glob('*.partial')), [])
        self.assertTrue(self.git.records[-1]['stdout_complete'])

    def test_missing_promisor_blob_does_not_trigger_lazy_fetch(self):
        subprocess.run(['git', '-C', str(self.repo), 'config', 'remote.origin.promisor', 'true'], check=True)
        subprocess.run(['git', '-C', str(self.repo), 'config', 'remote.origin.url',
                        'file:///definitely-absent-p21-fixture.git'], check=True)
        invalid = copy.deepcopy(self.parts)
        invalid[0]['git_blob_sha'] = 'f' * 40
        with self.assertRaisesRegex(ValueError, 'Batch header'):
            self.run_assembly(invalid)
        record = self.git.records[-1]
        self.assertIn('--no-lazy-fetch', record['argv'])
        self.assertTrue(Path(record['stdout']['path']).read_bytes().startswith(b'f' * 40 + b' missing\n'))
        self.assertNotIn(b'could not fetch', Path(record['stderr']['path']).read_bytes())
        self.assertFalse(self.output.exists())

    def test_write_error_survives_close_error_and_owned_partial_is_removed(self):
        real_open = R.open_output

        class FailingWriter:
            def __init__(self, fd):
                self.inner = real_open(fd)

            def write(self, data):
                raise OSError(errno.ENOSPC, 'synthetic archive write failure')

            def close(self):
                self.inner.close()
                raise OSError(errno.EDQUOT, 'synthetic archive close failure')

        with mock.patch.object(R, 'open_output', side_effect=FailingWriter):
            with self.assertRaises(OSError) as error:
                self.run_assembly()
        self.assertEqual(error.exception.errno, errno.ENOSPC)
        self.assertFalse(self.output.exists())
        self.assertEqual(list(self.root.glob('*.partial')), [])
        self.assertTrue(self.git.records[-1]['stdout_complete'])

    def test_xz_original_checks_all_original_part_digests(self):
        self.assertTrue(hasattr(R, 'restore_original'), 'Lossless-original restoration is not implemented')
        stored = self.root / 'original.xz'
        stored.write_bytes(lzma.compress(b''.join(self.data), format=lzma.FORMAT_XZ,
                                        check=lzma.CHECK_CRC64, preset=6))
        result = R.restore_original(stored, self.parts, self.expected, self.output, self.helper)
        self.assertEqual(self.output.read_bytes(), b''.join(self.data))
        self.assertEqual(len(result['verified_parts']), 2)
        self.assertEqual(result['status'], 'VERIFIED_LOSSLESS_ORIGINAL')
        corrupt = copy.deepcopy(self.parts)
        corrupt[1]['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Original xz part digest'):
            R.restore_original(stored, corrupt, self.expected, self.root / 'bad-original', self.helper)
        self.assertFalse((self.root / 'bad-original').exists())

    def test_truncated_xz_does_not_install_even_when_original_bytes_decode(self):
        self.assertTrue(hasattr(R, 'restore_original'), 'Lossless-original restoration is not implemented')
        stored = self.root / 'truncated.xz'
        stored.write_bytes(lzma.compress(b''.join(self.data))[:-8])
        with self.assertRaises((EOFError, ValueError, lzma.LZMAError)):
            R.restore_original(stored, self.parts, self.expected, self.output, self.helper)
        self.assertFalse(self.output.exists())
        self.assertEqual(list(self.root.glob('*.partial')), [])


if __name__ == '__main__':
    unittest.main(verbosity=2)
