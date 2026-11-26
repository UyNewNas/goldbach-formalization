#!/usr/bin/env python3
"""Focused structural checks. Synthetic final receipts carry no proof credit."""
import copy
import hashlib
import json
from pathlib import Path
import runpy
import sys
import tarfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
CONTINUATION = ROOT / 'docs/verification/20261126-p2-5-continuation'
DEFAULT_DRIVER = Path(__file__).with_name('run_cell00_five_consumers_v3.py')
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
PREVIOUS_PATH = ROOT / 'docs/verification/20261126-p2-5-resumed/field-final-attempt004/RESULT.json'
PREVIOUS = json.loads(PREVIOUS_PATH.read_text())
assert hashlib.sha256(PREVIOUS_PATH.read_bytes()).hexdigest() == 'c8f52525af889be955ffaa245d40ead84f560fea0de0f04e53ae202afeaab1f2'


class ContinuationStructure(unittest.TestCase):
    def api(self, name):
        self.assertTrue(name in NS, f'Missing attempt005 continuation interface: {name}')
        return NS[name]

    def fixture(self):
        self.api('validate_previous_final')
        target = NS['FIELD_TARGET']
        old_owners = NS['REUSED_FIELD_OWNERS']
        origin = {m: PRIOR if m in NS['REUSED_FIELD_OBJECTS'] else SPLIT for m in old_owners}
        final_owner = copy.deepcopy(SPLIT['modules'][target])
        final_owner.update(accepted=True, status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                           source_origin={'commit': NS['FIELD_PUBLICATION'], 'path': NS['FINAL_SOURCE_REL'],
                                          'sha256': NS['FINAL_SOURCE_SHA']})
        row = {
            'schema': 'p25-cell00-field-final-strict-v1', 'status': 'FINAL_FIELD_TYPED_DECODE_ACCEPTED',
            'accepted': True, 'publication_commit': NS['FIELD_PUBLICATION'], 'module_order': [target],
            'modules': {target: final_owner}, 'dependency_modules_compiled': [],
            'existing_owners_normally_recompiled': [], 'accepted_dependency_gates_rerun': [],
            'failed_same_name_field_object_used': False, 'failed_aggregate_relabelled_as_success': False,
            'public_final_statements_unchanged': True, 'private_scoped_simp_interface_checked': True,
            'raw_root_typed_decode_proved': True, 'original_archive_decode_proved': False,
            'Q96_proved': False, 'P2_5_proved': False, 'complete_external_after_matches_before': True,
            'historical_missing_external_hashes_invented': False,
            'reused_original_owner_receipts': {m: copy.deepcopy(origin[m]['modules'][m]) for m in old_owners},
            'reused_complete_context_validations': copy.deepcopy(SPLIT['additional_reuse_validations']),
            'source_receipt_by_reused_owner': {
                m: {'path': str(NS['PRIOR_FIELD'] if m in NS['REUSED_FIELD_OBJECTS'] else NS['SPLIT']) + '/RESULT.json',
                    'sha256': NS['PRIOR_FIELD_RESULT_SHA'] if m in NS['REUSED_FIELD_OBJECTS'] else NS['SPLIT_RESULT_SHA'],
                    'publication_commit': origin[m]['publication_commit'],
                    'aggregate_accepted': False, 'aggregate_status': 'MODULE_STAGE_FAILED', 'owner_accepted': True}
                for m in old_owners},
            'failed_split_receipt': copy.deepcopy(PREVIOUS['failed_split_receipt']),
            'prior_failed_final_owner': copy.deepcopy(SPLIT['modules'][target]),
            'repair_kind': 'explicit-field-composition-after-attempt004',
            'previous_final_attempt': {'path': str(NS['PREVIOUS_FINAL'] / 'RESULT.json'),
                'sha256': NS['PREVIOUS_FINAL_RESULT_SHA'], 'publication_commit': NS['PREVIOUS_FINAL_PUBLICATION'],
                'aggregate_accepted': False, 'aggregate_status': 'MODULE_STAGE_FAILED', 'failed_owner_reused': False},
            'previous_final_failed_owner': copy.deepcopy(PREVIOUS['modules'][target]),
        }
        return row

    def test_preserved_history_structure_is_accepted(self):
        field = self.fixture()
        self.api('validate_field_history')(field, SPLIT, PRIOR)
        self.api('validate_previous_final')(field, PREVIOUS, SPLIT, PRIOR)

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
        sources = self.api('select_explicit_sources')(SELECTION, FINAL_SELECTION, EXPLICIT_OVERRIDE)
        changed = [m for m in sources if sources[m] != SELECTION['source_graph'][m]]
        self.assertEqual(changed, [NS['FIELD_TARGET']])
        self.assertEqual(len(sources), 45)
        self.assertEqual(sources[NS['FIELD_TARGET']], EXPLICIT_OVERRIDE['source_spec'])

    def test_source_selection_rejects_changed_old_owner(self):
        final = copy.deepcopy(FINAL_SELECTION)
        final['source_graph']['ImbalancedChen.P2Saving16Cell00FieldBase']['source_sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'unchanged'):
            self.api('select_explicit_sources')(SELECTION, final, EXPLICIT_OVERRIDE)

    def test_source_selection_rejects_changed_import_api(self):
        final = copy.deepcopy(FINAL_SELECTION)
        final['source_graph'][NS['FIELD_TARGET']]['project_imports'] = []
        with self.assertRaisesRegex(RuntimeError, 'imports|API'):
            self.api('select_explicit_sources')(SELECTION, final, EXPLICIT_OVERRIDE)

    def test_previous_final_failure_cannot_be_relabelled(self):
        field = self.fixture()
        previous = copy.deepcopy(PREVIOUS)
        previous['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, '[Aa]ttempt004'):
            self.api('validate_previous_final')(field, previous, SPLIT, PRIOR)

    def test_previous_final_owner_identity_is_preserved(self):
        field = self.fixture()
        field['previous_final_failed_owner']['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, '[Aa]ttempt004'):
            self.api('validate_previous_final')(field, PREVIOUS, SPLIT, PRIOR)

    def test_explicit_override_cannot_change_public_api(self):
        override = copy.deepcopy(EXPLICIT_OVERRIDE)
        override['source_spec']['public_names'] = []
        with self.assertRaisesRegex(RuntimeError, 'API'):
            self.api('select_explicit_sources')(SELECTION, FINAL_SELECTION, override)

    def test_missing_publication_blocks_before_any_mutation(self):
        main = NS['main']
        globals_ = main.__globals__
        saved_pin, saved_publication = globals_['FIELD_RESULT_SHA'], globals_['FIELD_PUBLICATION']
        saved_git = globals_['git']
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
        self.assertEqual(calls, [])

    def test_missing_pin_blocks_before_any_mutation(self):
        main = NS['main']
        globals_ = main.__globals__
        saved_pin = globals_['FIELD_RESULT_SHA']
        saved_git = globals_['git']
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
        self.assertEqual(calls, [])


if __name__ == '__main__':
    unittest.main()
