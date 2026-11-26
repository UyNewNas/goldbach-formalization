#!/usr/bin/env python3
"""Small real-Git safety checks; no P2 checkout, cloud call, or Lean process."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile
import types
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def load(path, name):
    value = types.ModuleType(name)
    value.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), value.__dict__)
    return value


a = load(HERE / 'recover_p2_baseline_documents.py', 'baseline_adapter_test')
h = a.load_checked((ROOT / a.V3_PATH).read_bytes(), a.V3_SHA, ROOT / a.V3_PATH, 'baseline_v3_test')
h.GIT = a.GIT


class BaselineStorageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='p25-baseline-storage-test-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.owner = self.base / 'owner'
        self.owner.mkdir()
        a.git(['init', '-q'], self.owner)
        a.git(['config', 'extensions.worktreeConfig', 'true'], self.owner)
        a.git(['config', 'core.autocrlf', 'false'], self.owner)
        self.files = {
            a.PREFIX + 'discard.json': '{"example": 1}\n',
            a.PREFIX + 'literal [x]*? name.raw': 'literal path\n',
            a.PREFIX + 'protected-by-link.txt': 'source target\n',
            a.PREFIX + 'protected-receipt.json': '{}\n',
            a.PREFIX + 'protected-subtree/data.raw': 'kept directory\n',
            a.PREFIX + 'source.lean': '-- retained\n',
            a.PREFIX + 'script.py': 'print("retained")\n',
            a.PREFIX + 'object.olean': 'retained object\n',
            a.PREFIX + '.lake/input.json': '{}\n',
            a.PREFIX + '.gitattributes': '# retained\n',
            a.PREFIX + 'hardlinked.raw': 'shared inode\n',
            'ImbalancedChen/Proof.lean': '-- canonical retained\n',
            'outside.txt': 'outside prefix retained\n',
            '.gitignore': '*.ignored\n',
        }
        for name, value in self.files.items():
            path = self.owner / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(value)
        (self.owner / 'ImbalancedChen/Alias.lean').symlink_to('../' + a.PREFIX + 'protected-by-link.txt')
        a.git(['add', '--all'], self.owner)
        a.git(['-c', 'user.name=Fixture', '-c', 'user.email=fixture@invalid', 'commit', '-qm', 'fixture'], self.owner)
        self.root = self.base / 'baseline'
        a.git(['worktree', 'add', '--detach', str(self.root), 'HEAD'], self.owner)
        (self.root / 'keep.ignored').write_text('ignored bytes\n')
        (self.root / 'untracked.txt').write_text('untracked bytes\n')
        os.link(self.root / (a.PREFIX + 'hardlinked.raw'), self.base / 'shared-inode')
        _, self.rows = h.stages(self.root)
        target, links = h.fs_resolution(self.root / 'ImbalancedChen/Alias.lean')
        self.protected = {str(target.relative_to(self.root)), a.PREFIX + 'protected-receipt.json'}
        self.assertEqual(len(links), 1)

    def selection(self):
        return a.qualify_candidates(h, self.root, self.rows, self.protected,
                                    {a.PREFIX + 'protected-subtree/'})

    def test_exact_sparse_omission_preserves_sources_links_untracked_and_git_blobs(self):
        before = h.inventory(self.root)
        untracked = a.untracked(h, self.root)
        common_before = (self.owner / '.git/config').read_bytes()
        objects_before = h.inventory(self.owner / '.git/objects')
        head_before = a.git(['rev-parse', 'HEAD'], self.root)
        staged_before, _ = h.stages(self.root)
        selected = self.selection()
        self.assertEqual(set(selected), {a.PREFIX + 'discard.json', a.PREFIX + 'literal [x]*? name.raw'})
        self.assertGreater(sum(r['conservative_allocated_bytes'] for r in selected.values()), 0)
        rules = a.exact_rules(selected)
        output = self.base / 'evidence'
        output.mkdir()
        rulefile = output / 'rules'
        rulefile.write_bytes(rules)
        result = a.git(['sparse-checkout', 'check-rules', '--no-cone', '--rules-file', str(rulefile), '-z'],
                       self.root, b'\0'.join(os.fsencode(n) for n in self.rows) + b'\0')
        included = {os.fsdecode(x) for x in result.split(b'\0') if x}
        self.assertEqual(set(self.rows) - included, set(selected))
        a.apply_sparse(self.root, rules, output)
        ordinary = lambda data: {p:v for p,v in data.items() if v['kind'] != 'directory'}
        self.assertEqual(ordinary(h.inventory(self.root)), {p:v for p,v in ordinary(before).items() if p not in selected})
        self.assertEqual(a.untracked(h, self.root), untracked)
        self.assertEqual(h.inventory(self.owner / '.git/objects'), objects_before)
        self.assertEqual((self.owner / '.git/config').read_bytes(), common_before)
        self.assertEqual(a.git(['rev-parse', 'HEAD'], self.root), head_before)
        self.assertEqual(h.stages(self.root)[0], staged_before)
        self.assertEqual(a.git(['status', '--porcelain', '--untracked-files=no'], self.root), b'')
        for name, value in selected.items():
            self.assertFalse(os.path.lexists(self.root / name))
            raw = a.git(['cat-file', 'blob', value['git_blob_sha1']], self.root)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), value['sha256'])

    def test_changed_working_bytes_stop_before_sparse_mutation(self):
        name = a.PREFIX + 'discard.json'
        (self.root / name).write_text('changed\n')
        before = h.inventory(self.root)
        with self.assertRaisesRegex(RuntimeError, 'differs from its indexed HEAD blob'):
            self.selection()
        self.assertEqual(h.inventory(self.root), before)

    def test_unavailable_local_blob_stops_before_sparse_mutation(self):
        name = a.PREFIX + 'discard.json'
        oid = self.rows[name]['oid']
        (self.owner / '.git/objects' / oid[:2] / oid[2:]).unlink()
        before = h.inventory(self.root)
        with self.assertRaisesRegex(RuntimeError, 'Git failed'):
            self.selection()
        self.assertEqual(h.inventory(self.root), before)

    def test_apply_requires_successful_readonly_result_bound_to_plan(self):
        folder = self.base / 'prior-plan'
        folder.mkdir()
        plan = folder / 'PLAN.json'
        plan.write_text('{}\n')
        plan_sha, runner_sha = a.digest(plan.read_bytes()), '1' * 64
        receipt = {'status': 'READ_ONLY_PLAN_PREPARED', 'ended_utc': 'fixture',
                   'apply_requested': False, 'mutation_started': False,
                   'runner_sha256': runner_sha, 'plan_sha256': plan_sha}
        result = folder / 'RESULT.json'
        result.write_text(json.dumps(receipt))
        with self.assertRaisesRegex(RuntimeError, 'did not finish successfully'):
            a.verified_readonly_result(plan, plan_sha, runner_sha)
        receipt['status'] = 'READ_ONLY_PLAN_VERIFIED'
        result.write_text(json.dumps(receipt))
        self.assertEqual(a.verified_readonly_result(plan, plan_sha, runner_sha), a.digest(result.read_bytes()))
        receipt['plan_sha256'] = '0' * 64
        result.write_text(json.dumps(receipt))
        with self.assertRaisesRegex(RuntimeError, 'did not finish successfully'):
            a.verified_readonly_result(plan, plan_sha, runner_sha)


if __name__ == '__main__':
    unittest.main(verbosity=2)
