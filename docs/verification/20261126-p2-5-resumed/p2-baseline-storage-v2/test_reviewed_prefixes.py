#!/usr/bin/env python3
"""One real-Git regression for the newly reviewed five-prefix scope."""
from pathlib import Path
import hashlib
import os
import tempfile
import types
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
module = types.ModuleType('baseline_v2_scope_fixture')
module.__file__ = str(HERE / 'recover_p2_baseline_documents_v2.py')
exec(compile(Path(module.__file__).read_bytes(), module.__file__, 'exec'), module.__dict__)
a = module
h = a.load_checked((ROOT / a.V3_PATH).read_bytes(), a.V3_SHA, ROOT / a.V3_PATH, 'baseline_v3_fixture')
h.GIT = a.GIT


class ReviewedPrefixes(unittest.TestCase):
    def test_only_five_published_document_roots_are_omitted(self):
        self.assertEqual(a.PREFIXES, (
            'docs/source-only/', 'proof-continuation-data/',
            'verification/proof-continuation/', 'verification/parts/',
            'docs/evidence/owned-frontiers/',
        ))
        with tempfile.TemporaryDirectory(prefix='p25-five-prefix-fixture-') as folder:
            parent = Path(folder)
            owner = parent / 'owner'
            owner.mkdir()
            a.git(['init', '-q'], owner)
            a.git(['config', 'extensions.worktreeConfig', 'true'], owner)
            a.git(['config', 'core.autocrlf', 'false'], owner)
            files = {'.gitignore': '*.ignored\n', 'ImbalancedChen/Keep.lean': '-- keep\n',
                     'docs/evidence/external-native-pnt/untouched.json': '{}\n',
                     'verification/part2/untouched.json': '{}\n'}
            for prefix in a.PREFIXES:
                files.update({prefix + 'discard.json': '{"stored":true}\n',
                              prefix + 'keep.lean': '-- keep source\n',
                              prefix + 'keep.py': 'print("keep script")\n',
                              prefix + 'protected.json': '{"protected":true}\n',
                              prefix + 'subtree/data.raw': 'retained subtree\n',
                              prefix + '.lake/retained.json': '{}\n'})
            for name, content in files.items():
                path = owner / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            (owner / 'EvidenceAlias.txt').symlink_to(a.PREFIXES[0] + 'protected.json')
            a.git(['add', '--all'], owner)
            a.git(['-c', 'user.name=Fixture', '-c', 'user.email=fixture@invalid',
                   'commit', '-qm', 'five-prefix fixture'], owner)
            baseline = parent / 'baseline'
            a.git(['worktree', 'add', '--detach', str(baseline), 'HEAD'], owner)
            (baseline / 'keep.ignored').write_text('ignored\n')
            (baseline / 'untracked.txt').write_text('untracked\n')
            _, rows = h.stages(baseline)
            before = h.inventory(baseline)
            objects = h.inventory(owner / '.git/objects')
            selected = a.qualify_candidates(
                h, baseline, rows, {p + 'protected.json' for p in a.PREFIXES},
                {p + 'subtree/' for p in a.PREFIXES})
            expected = {p + 'discard.json' for p in a.PREFIXES}
            self.assertEqual(set(selected), expected)
            output = parent / 'evidence'
            output.mkdir()
            rules = a.exact_rules(selected)
            a.apply_sparse(baseline, rules, output)
            ordinary = lambda values: {p: v for p, v in values.items() if v['kind'] != 'directory'}
            self.assertEqual(ordinary(h.inventory(baseline)),
                             {p: v for p, v in ordinary(before).items() if p not in expected})
            self.assertEqual(h.inventory(owner / '.git/objects'), objects)
            self.assertEqual(a.git(['status', '--porcelain', '--untracked-files=no'], baseline), b'')
            for name, record in selected.items():
                self.assertFalse(os.path.lexists(baseline / name))
                raw = a.git(['cat-file', 'blob', record['git_blob_sha1']], baseline)
                self.assertEqual(hashlib.sha256(raw).hexdigest(), record['sha256'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
