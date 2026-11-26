#!/usr/bin/env python3
"""Targeted new v8 boundaries only: no cloud scans, Lean, or settled suite."""
from pathlib import Path
import hashlib
import json
import os
import tempfile
import types
import unittest

HERE = Path(__file__).resolve().parent
RUNNER = HERE.parent / 'run_cell00_four_consumers_v8.py'
BASELINE = HERE.parent / 'run_cell00_four_consumers_v7.py'
source = RUNNER if RUNNER.exists() else BASELINE
driver = types.ModuleType('fresh_context_under_test')
driver.__file__ = str(source)
exec(compile(source.read_bytes(), str(source), 'exec'), driver.__dict__)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class FreshContextBoundaries(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='p25-v8-boundary-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def need(self, name):
        function = getattr(driver, name, None)
        self.assertTrue(callable(function), 'Missing reviewed v8 boundary: ' + name)
        return function

    def exceptions(self):
        return [{'path': str(self.root / ('old-' + str(i)) / 'COMPLETE_EXTERNAL_BEFORE.json'),
                 'bytes': 4302154, 'sha256': sha(('original envelope ' + str(i)).encode())}
                for i in range(5)]

    def test_five_exact_absent_envelopes_are_ledger_gaps_not_frozen_inputs(self):
        inspect = self.need('inspect_history_requirements')
        exceptions = self.exceptions()
        requirements = {row['path']: row['sha256'] for row in exceptions}
        result = inspect(requirements, exceptions, {})
        self.assertEqual(result['frozen'], {})
        self.assertEqual(result['archive_gaps'], exceptions)
        self.assertEqual(result['pending_object_paths'], {})

    def test_sixth_missing_file_and_same_basename_wrong_tuple_are_rejected(self):
        inspect = self.need('inspect_history_requirements')
        exceptions = self.exceptions()
        requirements = {row['path']: row['sha256'] for row in exceptions}
        requirements[str(self.root / 'sixth/COMPLETE_EXTERNAL_BEFORE.json')] = '1' * 64
        with self.assertRaisesRegex(RuntimeError, 'Unapproved missing historical'):
            inspect(requirements, exceptions, {})
        requirements.pop(str(self.root / 'sixth/COMPLETE_EXTERNAL_BEFORE.json'))
        requirements[exceptions[0]['path']] = '2' * 64
        with self.assertRaisesRegex(RuntimeError, 'historical envelope tuple'):
            inspect(requirements, exceptions, {})
        requirements[exceptions[0]['path']] = exceptions[0]['sha256']
        exceptions[0]['bytes'] += 1
        with self.assertRaisesRegex(RuntimeError, 'historical envelope tuple'):
            inspect(requirements, exceptions, {})

    def test_mutated_original_owner_commands_cannot_pass_historical_hash(self):
        inspect = self.need('inspect_history_requirements')
        path = self.root / 'RESULT.json'
        original = json.dumps({'owner': {'command': ['lean', '-DwarningAsError=true']}}).encode()
        path.write_bytes(original)
        requirements = {str(path): sha(original)}
        self.assertEqual(inspect(requirements, [], {})['frozen'], requirements)
        path.write_text(json.dumps({'owner': {'command': ['lean']}}))
        with self.assertRaisesRegex(RuntimeError, 'Historical bytes differ'):
            inspect(requirements, [], {})

    def external_fixture(self):
        providers = [self.root / 'provider-a', self.root / 'provider-b']
        for path in providers:
            path.mkdir()
        obj = providers[0] / 'Example.olean'
        obj.write_bytes(b'object')
        companions = []
        for suffix in ('.private', '.server'):
            path = Path(str(obj) + suffix)
            path.write_bytes(suffix.encode())
            companions.append({'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path.read_bytes())})
        entries = [{'module': 'Example', 'object': {'path': str(obj), 'bytes': obj.stat().st_size,
                                                  'sha256': sha(obj.read_bytes())}, 'companions': companions}]
        return providers, entries

    def test_real_external_resolution_rejects_shadow_provider(self):
        resolve = self.need('resolve_external_entries')
        providers, entries = self.external_fixture()
        self.assertEqual(resolve(entries, providers), entries)
        (providers[1] / 'Example.olean').write_bytes(b'object')
        with self.assertRaisesRegex(RuntimeError, 'Missing or shadowed'):
            resolve(entries, providers)

    def test_companion_change_and_equal_count_wrong_module_are_rejected(self):
        resolve = self.need('resolve_external_entries')
        providers, entries = self.external_fixture()
        companion = Path(entries[0]['companions'][0]['path'])
        companion.write_bytes(b'changed!')
        with self.assertRaisesRegex(RuntimeError, 'External bytes differ'):
            resolve(entries, providers)
        companion.write_bytes(b'.private')
        entries[0]['module'] = 'WrongModule'
        with self.assertRaisesRegex(RuntimeError, 'Missing or shadowed'):
            resolve(entries, providers)

    def test_full_dag_traverses_cached_intermediary_before_filtering_missing(self):
        order = self.need('full_missing_order')
        objects = {'A': {'project_imports': ['B']}, 'B': {'project_imports': ['C']},
                   'C': {'project_imports': []}}
        self.assertEqual(order(objects, {'B'}, {'A', 'C'}), ['C', 'A'])
        # A cycle outside the missing nodes must still invalidate the full DAG.
        objects['D'] = {'project_imports': ['E']}
        objects['E'] = {'project_imports': ['D']}
        with self.assertRaisesRegex(RuntimeError, 'Cyclic'):
            order(objects, {'B', 'D', 'E'}, {'A', 'C'})

    def test_available_owner_cannot_become_a_normal_compiler_target(self):
        check = self.need('validate_normal_candidate')
        with self.assertRaisesRegex(RuntimeError, 'available accepted object'):
            check('A', {'A'}, ['A'], self.root / 'A.olean')

    def test_mismatching_rematerialization_is_not_admitted(self):
        check = self.need('validate_rebuilt_object')
        obj = self.root / 'A.olean'
        obj.write_bytes(b'new bytes')
        with self.assertRaisesRegex(RuntimeError, 'New object SHA differs'):
            check(obj, sha(b'old accepted bytes'))
        self.assertEqual(list(self.root.iterdir()), [obj])

    def test_post_stage_linked_input_mutation_is_detected(self):
        check = self.need('verify_frozen')
        source, linked = self.root / 'source', self.root / 'linked'
        source.write_bytes(b'frozen input')
        os.link(source, linked)
        frozen = {str(source): sha(source.read_bytes())}
        check(frozen)
        linked.write_bytes(b'changed input')
        with self.assertRaisesRegex(RuntimeError, 'Frozen'):
            check(frozen)

    def test_missing_runtime_pin_is_not_an_archival_envelope_exception(self):
        inspect = self.need('inspect_history_requirements')
        missing = self.root / 'toolchain/lean'
        with self.assertRaisesRegex(RuntimeError, 'Unapproved missing historical'):
            inspect({str(missing): '1' * 64}, self.exceptions(), {})

    def test_missing_private_declaration_fails_existing_complete_inventory_gate(self):
        name = 'ImbalancedChen.Fixture'
        saved = driver.SOURCES
        driver.SOURCES = {name: {'project_imports': []}}
        self.addCleanup(setattr, driver, 'SOURCES', saved)
        public = {'module': name, 'name': name + '.public', 'axiom': False,
                  'partial': False, 'unsafe': False, 'axioms': []}
        private = '_private.' + name + '.0.privateLemma'
        log = self.root / 'AUDIT.log'
        log.write_text('P0_QUEUE_DECL ' + json.dumps(public) + '\n' +
                       'P0_QUEUE_INVENTORY ' + json.dumps({'module': name, 'serialized': [public['name'], private],
                                                         'environment': [public['name'], private]}) + '\n' +
                       'P0_QUEUE_IMPORTS ' + json.dumps([name]) + '\n')
        with self.assertRaisesRegex(RuntimeError, 'Incomplete serialized/environment/declaration inventory'):
            driver.read_audit(log, name)


if __name__ == '__main__':
    unittest.main(verbosity=2)
