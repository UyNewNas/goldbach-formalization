#!/usr/bin/env python3
"""Small synthetic checks for the new Git publication/receipt boundaries."""
from pathlib import Path
import importlib.util
import tempfile
import unittest
from unittest.mock import patch
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('cell01_git_transport', Path(__file__).with_name('git_transport.py'))
T = importlib.util.module_from_spec(spec)
spec.loader.exec_module(T)


class TransportBoundaryTests(unittest.TestCase):
    def test_wrong_repository_rejected_without_echoing_credentials(self):
        with self.assertRaisesRegex(RuntimeError, '^ORIGIN_NOT_AUTHORIZED_REPOSITORY$'):
            T.authorized_url('https://placeholder-user:placeholder-secret@github.com/unrelated/repository.git')

    def test_other_host_rejected(self):
        with self.assertRaisesRegex(RuntimeError, '^ORIGIN_NOT_AUTHORIZED_REPOSITORY$'):
            T.authorized_url('https://example.invalid/UyNewNas/goldbach-formalization.git')

    def test_existing_branch_is_not_reused(self):
        with patch.object(T, 'git', return_value=(0, ('f' * 40 + '\t' + T.REF + '\n').encode())):
            with self.assertRaisesRegex(RuntimeError, '^TRANSPORT_BRANCH_ALREADY_EXISTS$'):
                T.require_absent_branch(Path('/unused'))

    def test_missing_branch_requires_empty_remote_result(self):
        with patch.object(T, 'git', return_value=(2, b'unexpected output')):
            with self.assertRaisesRegex(RuntimeError, '^TRANSPORT_BRANCH_ALREADY_EXISTS$'):
                T.require_absent_branch(Path('/unused'))

    def test_commit_with_parent_is_rejected(self):
        with patch.object(T, 'text_git', return_value='tree ' + 'a' * 40 + '\nparent ' + 'b' * 40):
            with self.assertRaisesRegex(RuntimeError, '^TRANSPORT_COMMIT_HAS_PARENT$'):
                T.tree_inventory(Path('/unused'), 'c' * 40)

    def test_extra_tree_file_is_rejected(self):
        def text_git(repo, args, **kwargs):
            if args[:2] == ['cat-file', '-p']:
                return 'tree ' + 'a' * 40 + '\n\nmessage'
            return '0'
        with patch.object(T, 'text_git', side_effect=text_git), patch.object(T, 'git', return_value=(0, b'100644 blob ' + b'a' * 40 + b'\told-receipt.json\0')):
            with self.assertRaisesRegex(RuntimeError, '^TREE_WHITELIST_REJECTED$'):
                T.tree_inventory(Path('/unused'), 'c' * 40)

    def test_wrong_source_bytes_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'TRANSPORT.json'
            source.write_bytes(b'changed')
            with self.assertRaisesRegex(RuntimeError, '^EXACT_TRANSPORT_PIN_MISMATCH$'):
                T.pinned(source, 'TRANSPORT.json')


if __name__ == '__main__':
    unittest.main()
