#!/usr/bin/env python3
"""Accepted006 reuse plus actual consumer004 disk-failure and live-space recovery checks."""
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
import tarfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
CONTINUATION = ROOT / 'docs/verification/20261126-p2-5-continuation'
DEFAULT_DRIVER = Path(__file__).with_name('run_cell00_five_consumers_v5.py')
DRIVER = Path(sys.argv.pop(1)) if len(sys.argv) > 1 and sys.argv[1].endswith('.py') else DEFAULT_DRIVER
NS = runpy.run_path(str(DRIVER))


def receipt(name, expected):
    with tarfile.open(CONTINUATION / name) as archive:
        names = [member for member in archive.getnames() if member == 'RESULT.json' or member.endswith('/RESULT.json')]
        if len(names) != 1:
            raise AssertionError(f'Expected one original RESULT in {name}: {names}')
        data = archive.extractfile(names[0]).read()
    if hashlib.sha256(data).hexdigest() != expected:
        raise AssertionError('Historical receipt bytes changed: ' + name)
    return json.loads(data)


SPLIT = receipt('cell00_field_split_attempt003.tar.xz', '00ae4f5be311670b1538e934574a79b56ae0808253711ae1e0c606095d6dfdf0')
PRIOR = receipt('cell00_field_decode_attempt001.tar.gz', '86afeed917a3361c5457db1b7b3f4546d2e513531288adfab3d3a196ad38eac1')
SELECTION = json.loads((CONTINUATION / 'cell00-five-consumers/SOURCE_AND_RECEIPT_SELECTION.json').read_text())
FINAL_SELECTION = json.loads((CONTINUATION / 'cell00-field-final/SOURCE_AND_RECEIPT_SELECTION.json').read_text())
EXPLICIT_OVERRIDE = json.loads((ROOT / 'docs/source-only/20261126-p2-5-cell00-field-explicit/SOURCE_OVERRIDE.json').read_text())
PREVIOUS_PATH = ROOT / 'docs/verification/20261126-p2-5-resumed/field-explicit-attempt005/RESULT.json'
PREVIOUS = json.loads(PREVIOUS_PATH.read_text())
assert hashlib.sha256(PREVIOUS_PATH.read_bytes()).hexdigest() == '812f43171da6572a897020df007846c3dfd4776253c4e851824b91536380f716'
EARLIER_PATH = ROOT / 'docs/verification/20261126-p2-5-resumed/field-final-attempt004/RESULT.json'
EARLIER = json.loads(EARLIER_PATH.read_text())
assert hashlib.sha256(EARLIER_PATH.read_bytes()).hexdigest() == 'c8f52525af889be955ffaa245d40ead84f560fea0de0f04e53ae202afeaab1f2'
SYMBOLIC_OVERRIDE = json.loads((ROOT / 'docs/source-only/20261126-p2-5-cell00-field-symbolic/SOURCE_OVERRIDE.json').read_text())
ACTUAL_PATH = ROOT / 'docs/verification/20261126-p2-5-resumed/field-symbolic-attempt006/RESULT.json'
ACTUAL = json.loads(ACTUAL_PATH.read_text())
assert hashlib.sha256(ACTUAL_PATH.read_bytes()).hexdigest() == '82123af5bc4f1e9334da8f578de11147effe73da0a7ab90b55459abbb25bcb0e'


class ActualFieldArtifacts(unittest.TestCase):
    """Read existing actual evidence only; no compiler, replay, or audit is run."""

    @classmethod
    def setUpClass(cls):
        cls.module = NS['FIELD_TARGET']
        cls.owner = ACTUAL['modules'][cls.module]
        cls.sources = NS['select_symbolic_sources'](SELECTION, FINAL_SELECTION, EXPLICIT_OVERRIDE, SYMBOLIC_OVERRIDE)
        NS['read_audit'].__globals__['SOURCES'] = cls.sources
        cls.audit = ACTUAL_PATH.parent / 'P2Saving16Cell00FieldDecode/AUDIT.log'

    def check_record(self, data, record):
        self.assertEqual(len(data), record['bytes'])
        self.assertEqual(hashlib.sha256(data).hexdigest(), record['sha256'])

    def test_complete_export_exact_bytes(self):
        rows = json.loads(lzma.decompress((ACTUAL_PATH.parent / 'ACTUAL_EVIDENCE.json.xz').read_bytes()))
        self.assertEqual(len(rows), 5)
        self.assertEqual(len({row['name'] for row in rows}), 5)
        for row in rows:
            self.assertIn(row['encoding'], ['utf-8', 'base64'])
            data = row['content'].encode() if row['encoding'] == 'utf-8' else base64.b64decode(row['content'], validate=True)
            self.check_record(data, row)
            self.assertEqual(data, (ACTUAL_PATH.parent / row['name']).read_bytes())
        self.check_record(ACTUAL_PATH.read_bytes(), {'bytes': 4867343, 'sha256': NS['FIELD_RESULT_SHA']})
        self.check_record((ACTUAL_PATH.parent / 'artifacts/P2Saving16Cell00FieldDecode.olean').read_bytes(), self.owner['object'])
        self.assertEqual(self.owner['object_companions'], [])

    def test_actual_normal_replay_and_audit_log_commands(self):
        for label, row in self.owner['stages'].items():
            self.assertEqual(row['status'], 'PASSED')
            self.assertEqual(row['exit_code'], 0)
            self.assertIs(row['timed_out'], False)
            data = (ACTUAL_PATH.parent / 'P2Saving16Cell00FieldDecode' / (label.upper() + '.log')).read_bytes()
            self.check_record(data, {'bytes': row['log_bytes'], 'sha256': row['log_sha256']})
        self.assertEqual((ACTUAL_PATH.parent / 'P2Saving16Cell00FieldDecode/NORMAL.log').read_bytes(), b'')
        tree = ast.parse(DRIVER.read_text())
        main = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'main')
        node = next(node for node in main.body if isinstance(node, ast.FunctionDef) and node.name == 'strict_commands')
        env = dict(NS['main'].__globals__)
        exec(compile(ast.Module(body=[node], type_ignores=[]), str(DRIVER), 'exec'), env)
        env['strict_commands'](self.owner['stages'], self.module, Path(self.owner['source_copy']['path']),
                               Path(self.owner['object']['path']), Path(self.owner['audit_source']['path']))

    def test_complete_owned_inventory_and_private_helper_from_actual_audit(self):
        records, inventory, imports = NS['read_audit'](self.audit, self.module)
        self.assertEqual(records, self.owner['owned_declarations'])
        self.assertEqual(len(records), self.owner['owned_count'])
        self.assertEqual(imports, self.owner['actual_project_closure'])
        self.assertEqual(len(imports), 18)
        self.assertEqual(len(records), 7)
        helper = NS['validate_private_composition'](ACTUAL)
        self.assertIn(helper, records)
        self.assertIn(helper['name'], inventory['serialized'])
        self.assertIn(helper['name'], inventory['environment'])
        self.assertEqual(helper['name'], NS['PRIVATE_HELPER_ACTUAL'])
        self.assertTrue(set(self.sources[self.module]['public_names']) <= {row['name'] for row in records})
        for content, key in [(records, 'declarations'), (inventory, 'inventory')]:
            data = (json.dumps(content, ensure_ascii=False, indent=2) + '\n').encode()
            self.check_record(data, self.owner[key])
        external = {name for name in NS['audited_imports'](self.audit) if not name.startswith('ImbalancedChen.')}
        self.assertEqual(external, set(ACTUAL['expected_external_imports']))
        self.assertEqual(len(external), 5312)

    def test_accepted_source_audit_template_and_immutable_source_scope(self):
        self.check_record((ROOT / NS['FINAL_SOURCE_REL']).read_bytes(), self.owner['source_copy'])
        payload_files = json.loads((ROOT / 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_FILES.json').read_text())
        audit_template = (ROOT / payload_files['audit_file']).read_text()
        self.check_record(audit_template.replace(NS['PAYLOAD'], self.module).encode(), self.owner['audit_source'])
        self.check_record((ROOT / 'docs/verification/20261126-p2-5-resumed/run_cell00_field_symbolic_cloud.py').read_bytes(), ACTUAL['runner'])
        self.assertEqual(ACTUAL['runner']['sha256'], NS['FIELD_RUNNER_SHA'])
        for module, row in self.sources.items():
            data = (ROOT / row['path']).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['source_sha256'])
            imports = [name for line in re.findall(r'^import\s+([^\n]+)$', data.decode(), re.M)
                       for name in line.split() if name.startswith('ImbalancedChen.')]
            self.assertEqual(imports, row['project_imports'])
        self.assertEqual(len(self.sources), 45)
        self.assertEqual(len(set(self.sources) - set(NS['FRESH_MODULES'])), 40)
        self.assertEqual(sum(len(self.sources[module]['public_names']) for module in NS['FRESH_MODULES']), 20)
        self.assertTrue(all(self.sources[module] == SELECTION['source_graph'][module] for module in NS['FRESH_MODULES']))
        self.assertEqual(SELECTION['expected_project_closures'],
                         {module: sorted(NS['project_closure'](module)) for module in NS['FRESH_MODULES']})
        self.assertEqual(ACTUAL['source_graph'], {module: self.sources[module] for module in FINAL_SELECTION['source_graph']})
        self.assertEqual(ACTUAL['source_override_details'], SYMBOLIC_OVERRIDE)
        self.assertEqual(PREVIOUS['source_graph'], {**FINAL_SELECTION['source_graph'], self.module: EXPLICIT_OVERRIDE['source_spec']})
        self.assertEqual(EARLIER['source_graph'], FINAL_SELECTION['source_graph'])

    def test_recorded_dependencies_runtime_and_distinct_failure_logs(self):
        self.assertEqual(len(ACTUAL['dependency_objects']), 21)
        self.assertEqual(set(ACTUAL['dependency_objects']), set(ACTUAL['source_graph']) - {self.module})
        self.assertEqual(ACTUAL['strict_flags'], NS['FLAGS'])
        for module, row in ACTUAL['dependency_objects'].items():
            self.assertEqual(row['source_sha256'], self.sources[module]['source_sha256'])
            self.assertEqual(ACTUAL['frozen_inputs'][row['path']], row['sha256'])
            self.assertEqual(ACTUAL['frozen_inputs'][row['isolated_path']], row['sha256'])
            self.assertEqual(row['sha256'], PREVIOUS['dependency_objects'][module]['sha256'])
            self.assertEqual(row['sha256'], EARLIER['dependency_objects'][module]['sha256'])
        external_hashes = {p: h for p, h in ACTUAL['frozen_inputs'].items()
                           if p.startswith('/mathlib/') or '/lib/lean/' in p}
        self.assertEqual(len(external_hashes), 5312 + 10624)
        for container in [SPLIT, EARLIER, PREVIOUS]:
            self.assertEqual(container['runtime'], ACTUAL['runtime'])
            self.assertEqual(container['strict_flags'], ACTUAL['strict_flags'])
            self.assertEqual(container['approved_LEAN_PATH'].split(':')[1:], ACTUAL['approved_LEAN_PATH'].split(':')[1:])
            self.assertTrue(all(container['frozen_inputs'].get(p) == h for p, h in external_hashes.items()))
        for path, container, key, size in [(PREVIOUS_PATH, PREVIOUS, 'PREVIOUS_FINAL_NORMAL_SHA', 192),
                                           (EARLIER_PATH, EARLIER, 'EARLIER_FINAL_NORMAL_SHA', 487)]:
            row = container['modules'][self.module]['stages']['normal']
            self.assertEqual(row['log_sha256'], NS[key])
            self.assertEqual(row['exit_code'], 1)
            self.assertIs(row['timed_out'], False)
            self.check_record((path.parent / 'P2Saving16Cell00FieldDecode/NORMAL.log').read_bytes(),
                              {'bytes': size, 'sha256': NS[key]})
        self.assertIs(ACTUAL['complete_external_after_matches_before'], True)
        self.assertEqual(ACTUAL['accepted_dependency_gates_rerun'], [])
        self.assertIs(ACTUAL['Q96_proved'], False)
        self.assertIs(ACTUAL['P2_5_proved'], False)

    def test_inherited_verifiers_and_gate_helpers_are_unchanged(self):
        old = ast.parse((ROOT / NS['ADAPTED_FROM_REL']).read_text())
        new = ast.parse(DRIVER.read_text())
        old_top = {n.name: n for n in old.body if isinstance(n, ast.FunctionDef)}
        new_top = {n.name: n for n in new.body if isinstance(n, ast.FunctionDef)}
        unchanged = ['require', 'digest', 'now', 'git', 'record_file', 'project_closure',
                     'read_audit', 'audited_imports', 'read_private_scope_audit', 'validate_field_history']
        for name in unchanged:
            self.assertEqual(ast.dump(old_top[name]), ast.dump(new_top[name]), name)
        old_nested = {n.name: n for n in old_top['main'].body if isinstance(n, ast.FunctionDef)}
        new_nested = {n.name: n for n in new_top['main'].body if isinstance(n, ast.FunctionDef)}
        self.assertEqual(set(old_nested), set(new_nested))
        self.assertEqual(len(old_nested), 15)
        for name in old_nested:
            self.assertEqual(ast.dump(old_nested[name]), ast.dump(new_nested[name]), name)


class ContinuationStructure(unittest.TestCase):
    def api(self, name):
        self.assertTrue(name in NS, f'Missing accepted006 continuation interface: {name}')
        return NS[name]

    def fixture(self):
        self.api('validate_earlier_final')
        self.api('validate_private_composition')
        return copy.deepcopy(ACTUAL)

    def test_preserved_history_structure_is_accepted(self):
        field = self.fixture()
        self.api('validate_field_history')(field, SPLIT, PRIOR)
        self.api('validate_previous_final')(field, PREVIOUS, SPLIT, PRIOR)
        self.api('validate_earlier_final')(field, PREVIOUS, EARLIER)
        self.api('validate_private_composition')(field)

    def test_split_aggregate_cannot_be_relabelled(self):
        field = self.fixture()
        split = copy.deepcopy(SPLIT)
        split['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, 'failed split'):
            NS['validate_field_history'](field, split, PRIOR)

    def test_old_owner_cannot_be_relabelled(self):
        field = self.fixture()
        module = NS['SPLIT_ACCEPTED_MODULES'][0]
        field['reused_original_owner_receipts'][module]['source_origin']['commit'] = NS['FIELD_PUBLICATION']
        with self.assertRaisesRegex(RuntimeError, 'provenance'):
            NS['validate_field_history'](field, SPLIT, PRIOR)

    def test_supplemental_context_cannot_be_replaced(self):
        field = self.fixture()
        module = next(iter(NS['REUSED_FIELD_OBJECTS']))
        field['reused_complete_context_validations'][module]['normal_recompiled'] = True
        with self.assertRaisesRegex(RuntimeError, 'supplemental'):
            NS['validate_field_history'](field, SPLIT, PRIOR)

    def test_source_selection_changes_only_final_owner(self):
        sources = self.api('select_symbolic_sources')(SELECTION, FINAL_SELECTION, EXPLICIT_OVERRIDE, SYMBOLIC_OVERRIDE)
        changed = [m for m in sources if sources[m] != SELECTION['source_graph'][m]]
        self.assertEqual(changed, [NS['FIELD_TARGET']])
        self.assertEqual(len(sources), 45)
        self.assertEqual(sources[NS['FIELD_TARGET']], SYMBOLIC_OVERRIDE['source_spec'])

    def test_source_selection_rejects_changed_old_owner(self):
        final = copy.deepcopy(FINAL_SELECTION)
        final['source_graph']['ImbalancedChen.P2Saving16Cell00FieldBase']['source_sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'unchanged'):
            self.api('select_symbolic_sources')(SELECTION, final, EXPLICIT_OVERRIDE, SYMBOLIC_OVERRIDE)

    def test_source_selection_rejects_changed_import_api(self):
        final = copy.deepcopy(FINAL_SELECTION)
        final['source_graph'][NS['FIELD_TARGET']]['project_imports'] = []
        with self.assertRaisesRegex(RuntimeError, 'imports|API'):
            self.api('select_symbolic_sources')(SELECTION, final, EXPLICIT_OVERRIDE, SYMBOLIC_OVERRIDE)

    def test_previous_final_failure_cannot_be_relabelled(self):
        field = self.fixture()
        previous = copy.deepcopy(PREVIOUS)
        previous['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, '[Aa]ttempt005'):
            self.api('validate_previous_final')(field, previous, SPLIT, PRIOR)

    def test_previous_final_owner_identity_is_preserved(self):
        field = self.fixture()
        field['previous_final_failed_owner']['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, '[Aa]ttempt005'):
            self.api('validate_previous_final')(field, PREVIOUS, SPLIT, PRIOR)

    def test_explicit_override_cannot_change_public_api(self):
        override = copy.deepcopy(EXPLICIT_OVERRIDE)
        override['source_spec']['public_names'] = []
        with self.assertRaisesRegex(RuntimeError, 'API'):
            self.api('select_symbolic_sources')(SELECTION, FINAL_SELECTION, override, SYMBOLIC_OVERRIDE)

    def test_missing_publication_blocks_before_any_mutation(self):
        main = NS['main']
        globals_ = main.__globals__
        saved_pin, saved_publication = globals_['FIELD_RESULT_SHA'], globals_['FIELD_PUBLICATION']
        saved_git = globals_['git']
        saved_review = globals_.get('FIELD_ARTIFACTS_REVIEWED')
        globals_['FIELD_ARTIFACTS_REVIEWED'] = True
        calls = []
        def forbidden_git(*args, **kwargs):
            calls.append((args, kwargs))
            raise AssertionError('Git reached before missing-publication rejection')
        globals_['FIELD_RESULT_SHA'] = '0' * 64
        globals_['FIELD_PUBLICATION'] = None
        globals_['git'] = forbidden_git
        try:
            with self.assertRaisesRegex(RuntimeError, 'SOURCE_ONLY'):
                main()
        finally:
            globals_['FIELD_RESULT_SHA'], globals_['FIELD_PUBLICATION'] = saved_pin, saved_publication
            globals_['git'] = saved_git
            globals_['FIELD_ARTIFACTS_REVIEWED'] = saved_review
        self.assertEqual(calls, [])

    def test_earlier_failed_owner_cannot_change(self):
        field = self.fixture()
        field['earlier_failed_final_owner']['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, '[Aa]ttempt004'):
            self.api('validate_earlier_final')(field, PREVIOUS, EARLIER)

    def test_new_private_helper_must_be_in_complete_owner(self):
        field = self.fixture()
        owner = field['modules'][NS['FIELD_TARGET']]
        owner['owned_declarations'] = [row for row in owner['owned_declarations'] if row['name'] != field['private_composition_helper_record']['name']]
        with self.assertRaisesRegex(RuntimeError, 'private|owned'):
            self.api('validate_private_composition')(field)

    def test_new_private_record_must_match_full_inventory(self):
        field = self.fixture()
        field['private_composition_helper_record']['name'] = '_private.not_the_actual_helper'
        with self.assertRaisesRegex(RuntimeError, 'private|owned'):
            self.api('validate_private_composition')(field)

    def test_missing_artifact_review_blocks_before_mutation(self):
        main = NS['main']
        globals_ = main.__globals__
        saved = {key: globals_.get(key) for key in ['FIELD_RESULT_SHA', 'FIELD_PUBLICATION', 'FIELD_ARTIFACTS_REVIEWED', 'git']}
        globals_['FIELD_RESULT_SHA'] = '0' * 64
        globals_['FIELD_PUBLICATION'] = '0' * 40
        globals_['FIELD_ARTIFACTS_REVIEWED'] = False
        calls = []
        def forbidden_git(*args, **kwargs):
            calls.append((args, kwargs))
            raise AssertionError('Git reached before artifact-review rejection')
        globals_['git'] = forbidden_git
        try:
            with self.assertRaisesRegex(RuntimeError, 'SOURCE_ONLY'):
                main()
        finally:
            globals_.update(saved)
        self.assertEqual(calls, [])

    def test_missing_pin_blocks_before_any_mutation(self):
        main = NS['main']
        globals_ = main.__globals__
        saved_pin = globals_['FIELD_RESULT_SHA']
        saved_git = globals_['git']
        saved_review = globals_.get('FIELD_ARTIFACTS_REVIEWED')
        globals_['FIELD_ARTIFACTS_REVIEWED'] = True
        calls = []
        def forbidden_git(*args, **kwargs):
            calls.append((args, kwargs))
            raise AssertionError('Git reached before missing-pin rejection')
        globals_['FIELD_RESULT_SHA'] = None
        globals_['git'] = forbidden_git
        try:
            with self.assertRaisesRegex(RuntimeError, 'SOURCE_ONLY'):
                main()
        finally:
            globals_['FIELD_RESULT_SHA'] = saved_pin
            globals_['git'] = saved_git
            globals_['FIELD_ARTIFACTS_REVIEWED'] = saved_review
        self.assertEqual(calls, [])


FAILED_CONSUMER_PATH = ROOT / 'docs/verification/20261126-p2-5-resumed/consumer-attempt004/RESULT.json'
FAILED_CONSUMER = json.loads(FAILED_CONSUMER_PATH.read_text())
assert hashlib.sha256(FAILED_CONSUMER_PATH.read_bytes()).hexdigest() == '2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a'


class DiskRecovery(unittest.TestCase):
    def function(self, name):
        self.assertTrue(name in NS, 'Missing v5 recovery interface: ' + name)
        return NS[name]

    def test_actual_failed_attempt_has_no_completed_or_started_gate(self):
        self.function('validate_failed_consumer')(FAILED_CONSUMER)
        self.assertEqual(FAILED_CONSUMER['source_graph'], ACTUAL['source_graph'] | {
            module: row for module, row in SELECTION['source_graph'].items() if module not in ACTUAL['source_graph']})

    def test_prior_accepted_owner_cannot_be_recompiled(self):
        failed = copy.deepcopy(FAILED_CONSUMER)
        failed['modules'][NS['FRESH_MODULES'][0]]['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, 'gate|owner|accepted'):
            self.function('validate_failed_consumer')(failed)

    def test_prior_started_stage_cannot_be_relabelled_as_no_execution(self):
        failed = copy.deepcopy(FAILED_CONSUMER)
        failed['modules'][NS['FRESH_MODULES'][0]]['stages']['normal'] = {'status': 'RUNNING'}
        with self.assertRaisesRegex(RuntimeError, 'gate|owner|stage'):
            self.function('validate_failed_consumer')(failed)

    def test_different_failure_does_not_authorize_resource_only_retry(self):
        failed = copy.deepcopy(FAILED_CONSUMER)
        failed['error'] = 'A different error'
        with self.assertRaisesRegex(RuntimeError, 'disk|space|failure'):
            self.function('validate_failed_consumer')(failed)

    def test_failed_target_object_is_not_reused(self):
        failed = copy.deepcopy(FAILED_CONSUMER)
        failed['modules'][NS['FRESH_MODULES'][0]]['object'] = {'sha256': '0' * 64}
        with self.assertRaisesRegex(RuntimeError, 'object|owner|gate'):
            self.function('validate_failed_consumer')(failed)

    def test_low_live_space_is_rejected(self):
        check = self.function('check_disk_space')
        module = check.__globals__['shutil']
        original = module.disk_usage
        class Usage:
            free = 0
        module.disk_usage = lambda path: Usage()
        try:
            with self.assertRaisesRegex(RuntimeError, 'DISK_SPACE'):
                check(1024, 'unit test; no filesystem mutation')
        finally:
            module.disk_usage = original

    def test_sufficient_live_space_is_recorded(self):
        check = self.function('check_disk_space')
        module = check.__globals__['shutil']
        original = module.disk_usage
        class Usage:
            free = 2370244608
        module.disk_usage = lambda path: Usage()
        try:
            row = check(1073741824, 'unit test; no filesystem mutation')
            self.assertEqual(row['free_bytes'], 2370244608)
            self.assertEqual(row['required_free_bytes'], 1073741824)
        finally:
            module.disk_usage = original

    def test_capacity_drop_after_initial_preflight_is_rejected(self):
        check = self.function('check_disk_space')
        module = check.__globals__['shutil']
        original = module.disk_usage
        class Usage:
            free = 2370244608
        usage = Usage()
        module.disk_usage = lambda path: usage
        try:
            check(1073741824, 'initial preflight')
            usage.free = 0
            with self.assertRaisesRegex(RuntimeError, 'DISK_SPACE'):
                check(1073741824, 'immediately before accepted dependency copying')
        finally:
            module.disk_usage = original

    def test_live_copy_guard_immediately_precedes_first_copy_loop(self):
        tree = ast.parse(DRIVER.read_text())
        main = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'main')
        body = next(node for node in main.body if isinstance(node, ast.Try)).body
        first_copy_loop = next(index for index, node in enumerate(body)
                               if isinstance(node, ast.For) and any(
                                   isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and
                                   call.func.id == 'copy_dependency' for call in ast.walk(node)))
        guard, persist = body[first_copy_loop - 2:first_copy_loop]
        calls = [node for node in ast.walk(guard) if isinstance(node, ast.Call)]
        checks = [call for call in calls if isinstance(call.func, ast.Name) and call.func.id == 'check_disk_space']
        self.assertEqual(len(checks), 1)
        self.assertEqual(ast.literal_eval(checks[0].args[1]), 'immediately before accepted dependency copying')
        self.assertIsInstance(checks[0].args[0], ast.Call)
        self.assertEqual(checks[0].args[0].func.id, 'max')
        self.assertEqual(persist.value.func.id, 'write')

    def test_all_v4_predicate_and_gate_helpers_are_unchanged(self):
        old = ast.parse((ROOT / 'docs/verification/20261126-p2-5-resumed/run_cell00_five_consumers_v4.py').read_text())
        new = ast.parse(DRIVER.read_text())
        old_top = {n.name: n for n in old.body if isinstance(n, ast.FunctionDef)}
        new_top = {n.name: n for n in new.body if isinstance(n, ast.FunctionDef)}
        for name in old_top.keys() - {'main'}:
            self.assertEqual(ast.dump(old_top[name]), ast.dump(new_top[name]), name)
        old_nested = {n.name: n for n in old_top['main'].body if isinstance(n, ast.FunctionDef)}
        new_nested = {n.name: n for n in new_top['main'].body if isinstance(n, ast.FunctionDef)}
        self.assertEqual(set(old_nested), set(new_nested))
        for name in old_nested:
            self.assertEqual(ast.dump(old_nested[name]), ast.dump(new_nested[name]), name)


if __name__ == '__main__':
    unittest.main()
