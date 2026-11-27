"""Genuine-input validation and fail-closed local regression checks only."""
import ast
import json
from pathlib import Path
import tempfile
import unittest

import build_v6 as builder
from main_delta import make_changes


class V6Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.context=builder.load_context(builder.PACKET/'PROBE_RESULT.json')
        cls.post=cls.context['source']
        for _,before,after in make_changes(cls.context):
            assert cls.post.count(before)==1
            cls.post=cls.post.replace(before,after)

    def test_actual_probe_and_one_token_source_delta(self):
        c=self.context
        self.assertEqual(c['amendment']['inserted_bytes'],'Finset.')
        self.assertEqual(len(c['new_source'])-len(c['old_source']),7)
        self.assertEqual(len(c['live']),8614)
        self.assertEqual(len(c['prefix']),5500)

    def test_extra_source_edit_is_rejected(self):
        c=self.context
        with self.assertRaises(builder.BuildError):
            builder.source_amendment(c['old_source'],c['new_source']+b'\n',c['contract'])

    def test_guard_rejects_unattributed_extra_failed_source(self):
        c=self.context
        extra=json.dumps(c['failed_source']).encode()+b'\n'
        with self.assertRaises(builder.BuildError):
            builder.validate_guard(c['prefix'],c['live']+extra,c['records'])

    def test_guard_rejects_changed_historical_success_boundary(self):
        c=self.context;records=json.loads(json.dumps(c['records']));records[1]['exit_code']=1
        with self.assertRaises(builder.BuildError):
            builder.validate_guard(c['prefix'],c['live'],records)

    def test_helpers_and_original_remaining_validation_sequence_unchanged(self):
        helpers=builder.validate_main_only(self.context['source'],self.post)
        self.assertEqual(len(helpers),27)
        weakened=self.post.replace("assert digest==known['identity']['sha256']","assert True")
        with self.assertRaises(builder.BuildError):builder.validate_main_only(self.context['source'],weakened)
        weakened=self.post.replace('assert bound_after==bound_before','assert bound_after>=0')
        with self.assertRaises(builder.BuildError):builder.validate_main_only(self.context['source'],weakened)

    def test_missing_actual_probe_never_creates_output(self):
        with tempfile.TemporaryDirectory(dir=builder.HERE) as directory:
            p=Path(directory);out=p/'no-output'
            with self.assertRaises(builder.BuildError):builder.build(p/'absent.json',out)
            self.assertFalse(out.exists())

    def test_frozen_v4_snapshot_preserve_hash_uses_written_prefix(self):
        tree=ast.parse(self.post)
        writes=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='combined_snapshot' and n.func.attr=='write_bytes']
        preserves=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='preserve' and n.args and isinstance(n.args[0],ast.Name) and n.args[0].id=='combined_snapshot']
        self.assertEqual(len(writes),1);self.assertEqual(len(preserves),1)
        written=writes[0].args[0]
        hashed=preserves[0].args[1].func.value.args[0]
        self.assertEqual(ast.dump(written),ast.dump(hashed))
        self.assertEqual(written.id,'v4_guard_prefix')


if __name__=='__main__':unittest.main()
