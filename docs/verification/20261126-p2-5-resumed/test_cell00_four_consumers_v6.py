#!/usr/bin/env python3
"""Offline guards for the actual partial v5 result and four-owner continuation."""
import ast
import base64
import copy
import hashlib
import json
import lzma
from pathlib import Path
import re
import runpy
import sys
import unittest

HERE = Path(__file__).resolve().parent
DRIVER = Path(sys.argv.pop(1)) if len(sys.argv) > 1 and sys.argv[1].endswith('.py') else HERE / 'run_cell00_four_consumers_v6.py'
saved_argv = sys.argv[:]
sys.argv = [str(HERE / 'test_cell00_five_consumers_v5.py'), str(DRIVER)]
try:
    BASE = runpy.run_path(str(HERE / 'test_cell00_five_consumers_v5.py'))
finally:
    sys.argv = saved_argv
NS, ROOT = BASE['NS'], BASE['ROOT']
ActualFieldArtifacts = BASE['ActualFieldArtifacts']
ContinuationStructure = BASE['ContinuationStructure']
DiskRecovery = BASE['DiskRecovery']
ACTUAL_PATH = HERE / 'consumer-attempt005/RESULT.json'
ACTUAL = json.loads(ACTUAL_PATH.read_text())
assert hashlib.sha256(ACTUAL_PATH.read_bytes()).hexdigest() == 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88'
OVERRIDE_PATH = ROOT / 'docs/source-only/20261126-p2-5-cell00-parse-transport/SOURCE_OVERRIDE.json'
OVERRIDE = json.loads(OVERRIDE_PATH.read_text())
DECODED = 'ImbalancedChen.P2Saving16Cell00Decoded'
PARSE = 'ImbalancedChen.P2Saving16Cell00OriginalParse'


class ActualPartialConsumer(unittest.TestCase):
    def function(self, name):
        self.assertIn(name, NS, 'Missing bounded continuation interface: ' + name)
        return NS[name]

    def check_record(self, data, row):
        self.assertEqual(len(data), row['bytes'])
        self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'])

    def test_actual_v5_failure_with_one_accepted_owner(self):
        self.function('validate_failed_parse')(ACTUAL, BASE['FAILED_CONSUMER'])
        self.assertEqual(ACTUAL['source_graph'], BASE['FAILED_CONSUMER']['source_graph'])
        self.assertEqual(len(ACTUAL['dependency_objects']), 40)
        self.assertEqual([m for m, owner in ACTUAL['modules'].items() if owner['accepted']], [DECODED])
        self.assertEqual(len(ACTUAL['frozen_inputs']), 16646)

    def test_complete_actual_capsule_and_accepted_object(self):
        rows = json.loads(lzma.decompress((ACTUAL_PATH.parent / 'ACTUAL_EVIDENCE.json.xz').read_bytes()))
        self.assertEqual(len(rows), 7)
        self.assertEqual(len({row['name'] for row in rows}), 7)
        for row in rows:
            self.assertIn(row['encoding'], ['utf-8', 'base64'])
            data = row['content'].encode() if row['encoding'] == 'utf-8' else base64.b64decode(row['content'], validate=True)
            self.check_record(data, row)
            self.assertEqual(data, (ACTUAL_PATH.parent / row['name']).read_bytes())
        owner = ACTUAL['modules'][DECODED]
        self.check_record((ACTUAL_PATH.parent / 'artifacts/P2Saving16Cell00Decoded.olean').read_bytes(), owner['object'])
        self.assertEqual(owner['object_companions'], [])

    def test_actual_decoded_logs_inventory_and_commands(self):
        sources = NS['select_symbolic_sources'](BASE['SELECTION'], BASE['FINAL_SELECTION'], BASE['EXPLICIT_OVERRIDE'], BASE['SYMBOLIC_OVERRIDE'])
        NS['read_audit'].__globals__['SOURCES'] = sources
        owner = ACTUAL['modules'][DECODED]
        for label, row in owner['stages'].items():
            self.check_record((ACTUAL_PATH.parent / DECODED.split('.')[-1] / (label.upper() + '.log')).read_bytes(),
                              {'bytes': row['log_bytes'], 'sha256': row['log_sha256']})
            self.assertEqual(row['status'], 'PASSED')
            self.assertEqual(row['exit_code'], 0)
            self.assertIs(row['timed_out'], False)
        audit_path = ACTUAL_PATH.parent / DECODED.split('.')[-1] / 'AUDIT.log'
        records, inventory, imports = NS['read_audit'](audit_path, DECODED)
        self.assertEqual(records, owner['owned_declarations'])
        self.assertEqual(len(records), owner['owned_count'])
        self.assertEqual(len(records), 4)
        self.assertEqual(imports, owner['actual_project_closure'])
        for content, key in [(records, 'declarations'), (inventory, 'inventory')]:
            self.check_record((json.dumps(content, ensure_ascii=False, indent=2) + '\n').encode(), owner[key])
        self.assertEqual({name for name in NS['audited_imports'](audit_path) if not name.startswith('ImbalancedChen.')},
                         set(ACTUAL['expected_external_imports']))
        tree = ast.parse(DRIVER.read_text())
        main = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'main')
        strict = next(node for node in main.body if isinstance(node, ast.FunctionDef) and node.name == 'strict_commands')
        env = dict(NS['main'].__globals__)
        exec(compile(ast.Module(body=[strict], type_ignores=[]), str(DRIVER), 'exec'), env)
        env['strict_commands'](owner['stages'], DECODED, Path(owner['source_copy']['path']),
                               Path(owner['object']['path']), Path(owner['audit_source']['path']))
        template = (ROOT / 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean').read_text()
        self.check_record(template.replace(NS['PAYLOAD'], DECODED).encode(), owner['audit_source'])
        self.check_record((ROOT / owner['source_origin']['path']).read_bytes(), owner['source_copy'])

    def test_failed_parse_full_log_is_preserved_without_object_credit(self):
        owner = ACTUAL['modules'][PARSE]
        stage = owner['stages']['normal']
        data = (ACTUAL_PATH.parent / PARSE.split('.')[-1] / 'NORMAL.log').read_bytes()
        self.check_record(data, {'bytes': 1046, 'sha256': NS['FAILED_PARSE_NORMAL_SHA']})
        self.assertEqual(stage['exit_code'], 1)
        self.assertIs(stage['timed_out'], False)
        self.assertEqual(data.count(b'(kernel) excessive memory consumption detected'), 2)
        self.assertIn(b'No goals to be solved', data)
        self.assertNotIn('object', owner)
        self.assertIs(owner['accepted'], False)
        self.assertIs(ACTUAL['accepted'], False)
        self.assertIs(ACTUAL['Q96_proved'], False)
        self.assertIs(ACTUAL['P2_5_proved'], False)

    def test_failed_aggregate_cannot_be_promoted(self):
        changed = copy.deepcopy(ACTUAL)
        changed['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, 'actual|failed|aggregate'):
            self.function('validate_failed_parse')(changed, BASE['FAILED_CONSUMER'])

    def test_decoded_must_remain_accepted_under_original_owner(self):
        for key, value in [('accepted', False), ('source_origin', {}), ('object', {'sha256': '0' * 64})]:
            changed = copy.deepcopy(ACTUAL)
            changed['modules'][DECODED][key] = value
            with self.assertRaises((RuntimeError, KeyError)):
                self.function('validate_failed_parse')(changed, BASE['FAILED_CONSUMER'])

    def test_failed_parse_cannot_supply_object_or_replay_credit(self):
        for key, value in [('accepted', True), ('object', {'sha256': '0' * 64}),
                           ('stages', {'normal': ACTUAL['modules'][PARSE]['stages']['normal'], 'replay': {'status': 'PASSED'}})]:
            changed = copy.deepcopy(ACTUAL)
            changed['modules'][PARSE][key] = value
            with self.assertRaises((RuntimeError, KeyError)):
                self.function('validate_failed_parse')(changed, BASE['FAILED_CONSUMER'])

    def test_pending_owner_cannot_be_mistaken_for_a_fresh_unrun_owner(self):
        changed = copy.deepcopy(ACTUAL)
        changed['modules'][NS['FRESH_MODULES'][2]]['stages'] = {'normal': {'status': 'PASSED'}}
        with self.assertRaisesRegex(RuntimeError, 'pending|stage|owner'):
            self.function('validate_failed_parse')(changed, BASE['FAILED_CONSUMER'])

    def test_missing_decoded_review_blocks_before_any_filesystem_access(self):
        main = NS['main']
        env = main.__globals__
        self.assertIn('DECODED_ARTIFACTS_REVIEWED', env)
        saved = {name: env[name] for name in ['DECODED_ARTIFACTS_REVIEWED', 'ROOT']}
        class ForbiddenRoot:
            def __getattr__(self, name):
                raise AssertionError('Filesystem reached before review gate: ' + name)
        env['DECODED_ARTIFACTS_REVIEWED'] = False
        env['ROOT'] = ForbiddenRoot()
        try:
            with self.assertRaisesRegex(RuntimeError, 'SOURCE_ONLY'):
                main()
        finally:
            env.update(saved)


class SymbolicParseAndScope(unittest.TestCase):
    def test_all_v5_verification_helpers_are_unchanged(self):
        old = ast.parse((HERE / 'run_cell00_five_consumers_v5.py').read_text())
        new = ast.parse(DRIVER.read_text())
        old_top = {node.name: node for node in old.body if isinstance(node, ast.FunctionDef)}
        new_top = {node.name: node for node in new.body if isinstance(node, ast.FunctionDef)}
        self.assertEqual(len(old_top) - 1, 18)
        for name in old_top.keys() - {'main'}:
            self.assertEqual(ast.dump(old_top[name]), ast.dump(new_top[name]), name)
        old_nested = {node.name: node for node in old_top['main'].body if isinstance(node, ast.FunctionDef)}
        new_nested = {node.name: node for node in new_top['main'].body if isinstance(node, ast.FunctionDef)}
        self.assertEqual(set(old_nested), set(new_nested))
        self.assertEqual(len(old_nested), 15)
        for name in old_nested:
            self.assertEqual(ast.dump(old_nested[name]), ast.dump(new_nested[name]), name)

    def test_exact_public_statements_imports_and_symbolic_helpers(self):
        old = (ROOT / OVERRIDE['previous_source']['path']).read_text()
        new = (ROOT / OVERRIDE['new_source']['path']).read_text()
        statements = lambda text: re.findall(r'^theorem\s+(\w+)\s*:(.*?)\s*:=\s*by', text, re.M | re.S)
        self.assertEqual(statements(old), statements(new))
        self.assertEqual(len(statements(new)), 3)
        self.assertEqual(re.findall(r'^import .*$', old, re.M), re.findall(r'^import .*$', new, re.M))
        self.assertEqual([PARSE + '.' + name for name in re.findall(r'^private theorem (\w+)', new, re.M)], NS['PARSE_PRIVATE_HELPERS'])
        self.assertEqual(len(NS['PARSE_PRIVATE_HELPERS']), 3)
        public_part = new[new.index('\ntheorem cell00_original_decode'):]
        self.assertNotRegex(public_part, r'\b(change|rw|rewrite|unfold|simp|rfl)\b')
        self.assertNotRegex(new, r'\b(sorry|admit|axiom|native_decide|unsafe)\b')
        self.assertNotIn('import ImbalancedChen.P2OriginalSaving16FiniteArchive', new)

    def test_only_parse_source_row_changes_and_private_helpers_must_be_audited(self):
        original = NS['select_symbolic_sources'](BASE['SELECTION'], BASE['FINAL_SELECTION'], BASE['EXPLICIT_OVERRIDE'], BASE['SYMBOLIC_OVERRIDE'])
        self.assertIn('select_parse_sources', NS)
        selected = NS['select_parse_sources'](original, OVERRIDE)
        self.assertEqual(len(selected), 45)
        self.assertEqual([module for module in selected if selected[module] != original[module]], [PARSE])
        for module, row in selected.items():
            self.assertEqual(hashlib.sha256((ROOT / row['path']).read_bytes()).hexdigest(), row['source_sha256'])
        self.assertEqual(selected[PARSE]['public_names'], original[PARSE]['public_names'])
        self.assertEqual(selected[PARSE]['project_imports'], original[PARSE]['project_imports'])
        self.assertIn('validate_parse_helpers', NS)
        with self.assertRaisesRegex(RuntimeError, 'private|helper|owned'):
            NS['validate_parse_helpers']([])

    def test_unreviewed_source_import_expansion_is_rejected(self):
        original = NS['select_symbolic_sources'](BASE['SELECTION'], BASE['FINAL_SELECTION'], BASE['EXPLICIT_OVERRIDE'], BASE['SYMBOLIC_OVERRIDE'])
        changed = copy.deepcopy(OVERRIDE)
        changed['source_spec']['project_imports'].append('ImbalancedChen.P2OriginalSaving16FiniteArchive')
        self.assertIn('select_parse_sources', NS)
        with self.assertRaisesRegex(RuntimeError, 'imports|scope|API'):
            NS['select_parse_sources'](original, changed)

    def test_only_four_missing_owners_can_execute_gates(self):
        self.assertIn('CONTINUATION_MODULES', NS)
        self.assertEqual(NS['CONTINUATION_MODULES'], NS['FRESH_MODULES'][1:])
        self.assertEqual([row['module'] for row in NS['MODULES']], NS['CONTINUATION_MODULES'])
        self.assertNotIn(DECODED, NS['CONTINUATION_MODULES'])
        self.assertEqual(len(set(ACTUAL['source_graph']) - set(NS['CONTINUATION_MODULES'])), 41)
        self.assertEqual(sum(len(ACTUAL['source_graph'][m]['public_names']) for m in NS['CONTINUATION_MODULES']), 17)
        tree = ast.parse(DRIVER.read_text())
        main = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'main')
        targets = [node.value for node in main.body if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'target_names' for t in node.targets)]
        self.assertEqual(len(targets), 1)
        self.assertEqual(ast.dump(targets[0]), ast.dump(ast.parse('set(CONTINUATION_MODULES)', mode='eval').body))


if __name__ == '__main__':
    unittest.main()
