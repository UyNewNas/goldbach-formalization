#!/usr/bin/env python3
"""Only new v3 boundaries; synthetic unit inputs are never saved as receipts."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import runpy
import sys
import tarfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
DRIVER = Path(sys.argv.pop(1)) if len(sys.argv) > 1 and sys.argv[1].endswith('.py') else HERE / 'run_canonical_cell01_v3.py'
NS = runpy.run_path(str(DRIVER))
OUTER_PATH = REPO / 'docs/source-only/20261125-p2-5-decoder/p3-actual/p25-unguarded-sources/attempt001/RUN_RESULT.json'
assert hashlib.sha256(OUTER_PATH.read_bytes()).hexdigest() == 'cb11eb092d12e3e1f08eb9dccad4ecbe53311f456babe6c0ccabe72b93c3fa65'
OUTER = json.loads(OUTER_PATH.read_text())
ROWS = json.loads((REPO / NS['INPUT_MANIFEST']).read_text())['saving16_inputs']
RECOVERY = json.loads((REPO / 'docs/source-only/20261126-p2-5-cache-rematerialization/RECOVERY_SELECTION.json').read_text())
SELECTION = json.loads((HERE.parent / 'cell00-fresh-context/FRESH_CONTEXT_SELECTION.json').read_text())
BOOTSTRAP_PATH = REPO / 'docs/source-only/20261126-p2-5-cache-rematerialization/bootstrap_receipts.py'
assert hashlib.sha256(BOOTSTRAP_PATH.read_bytes()).hexdigest() == '46fa4a87040115bd8a1fa59abb598836063363374c2878992e4b7ac6ad000293'
BOOTSTRAP = runpy.run_path(str(BOOTSTRAP_PATH))
BOOTSTRAP_SELECTION = json.loads(BOOTSTRAP_PATH.with_name('RECEIPT_BOOTSTRAP_SELECTION.json').read_text())
PREVIOUS_ROW = next(row for row in BOOTSTRAP_SELECTION['entries']
                    if row['target'] == SELECTION['inputs']['consumer005_receipt']['path'])
assert PREVIOUS_ROW['target_sha256'] == SELECTION['inputs']['consumer005_receipt']['sha256']
PREVIOUS = json.loads(BOOTSTRAP['decode_entry'](REPO, PREVIOUS_ROW))


def accounting_fixture():
    """A pure validator fixture, not a future actual successful v8 receipt."""
    module = SELECTION['normal_order'][0]
    row = RECOVERY['objects'][module]
    root = NS['CELL00_RESULT'].parent / 'rematerialization'
    obj = root / 'lib' / (module.replace('.', '/') + '.olean')
    source = root / 'src' / (module.replace('.', '/') + '.lean')
    witnesses = [{'path': x['realpath'], 'realpath': x['realpath'],
                  **{key: x[key] for key in ['sha256', 'bytes', 'device', 'inode', 'mtime_ns']}}
                 for x in RECOVERY['witnesses']]
    stage = {'module': module, 'status': 'PASSED', 'exit_code': 0, 'timed_out': False,
             'purpose': 'exact-historical-byte-rematerialization', 'cwd': str(NS['ROOT']),
             'LEAN_PATH': ':'.join([str(root / 'lib'), *SELECTION['external_provider_roots'][1:]]),
             'command': [str(NS['LEAN']), *RECOVERY['runtime']['strict_flags'],
                         '--root=' + str(root / 'src'), '-o', str(obj), str(source)],
             'expected_object_sha256': row['sha256'], 'exact_historical_object_match': True,
             'object': {'path': str(obj), 'bytes': 1, 'sha256': row['sha256']},
             'object_companions': [], 'input_snapshot_before': witnesses, 'input_snapshot_after': witnesses}
    receipt = {'schema': 'p25-exact-normal-rematerialization-fresh-context-v8',
               'status': 'EXACT_OBJECTS_READY_FOR_NEW_CONSUMER_CONTEXT', 'exact_objects_ready': True,
               'accepted': False, 'new_formal_credit': False, 'P2_5_proved': False,
               'publication_commit': NS['CELL00_PUBLICATION'], 'runner_sha256': NS['CELL00_RUNNER_SHA256'],
               'selection_sha256': NS.get('CELL00_SELECTION_SHA256'),
               'normal_stages': [stage], 'replay_stages': [], 'owned_audit_stages': [],
               'available_objects_reused_without_normal': sorted(set(RECOVERY['objects']) - {module}),
               'old_receipts_changed': False, 'old_snapshots_synthesized': False, 'old_v7_preflight_passed': False,
               'historical_archive_gaps': SELECTION['historical_envelope_exceptions']}
    workflow = {'normal_rematerialization_stages': [stage], 'dependency_modules_compiled': [module],
                'existing_owners_normally_recompiled': [module], 'consumer_phase_dependency_modules_compiled': [],
                'accepted_dependency_gates_rerun': [], 'historical_archive_gaps': receipt['historical_archive_gaps'],
                'dependency_objects': {m: {'sha256': d['sha256'], 'source_sha256': d['source_sha256']}
                                       for m, d in RECOVERY['objects'].items()}}
    return workflow, receipt


def context_fixture():
    """Reuse actual old entries in a labeled unit fixture; no new receipt is written."""
    archive = REPO / SELECTION['inputs']['upstream_snapshot_archive']['path']
    with tarfile.open(archive) as stream:
        data = stream.extractfile(SELECTION['upstream_snapshot']['member']).read()
    assert hashlib.sha256(data).hexdigest() == SELECTION['upstream_snapshot']['sha256']
    original = json.loads(data)
    runtime = {path: h for path, h in PREVIOUS['frozen_inputs'].items()
               if path.startswith(('/mathlib/', '/workspace/toolchains/'))}
    upstream = NS['ROOT'] / '.lake/diagnostic/p25-cell00-remaining-arithmetic-attempt001'
    descriptors = {key: {'path': str(upstream / filename), 'bytes': SELECTION[pin]['bytes'],
                         'sha256': SELECTION[pin]['sha256']}
                   for key, pin, filename in [
                       ('source_complete_snapshot', 'upstream_snapshot', 'COMPLETE_EXTERNAL_BEFORE.json'),
                       ('source_accepted_receipt', 'upstream_accepted_receipt', 'RESULT.json')]}
    base = {'schema': 'p25-actual-fresh-external-context-v8', 'provider_roots': original['provider_roots'],
            'entries': original['entries'], 'module_count': 5312, 'companion_count': 10624,
            'runtime_pin_count': 15940, 'historical_missing_hashes_invented': False,
            'started_utc': 'synthetic-unit-observation-not-a-receipt',
            'finished_utc': 'synthetic-unit-observation-not-a-receipt', **descriptors}
    contexts = [dict(copy.deepcopy(base), phase=phase) for phase in [
        'before-normal-rematerialization', 'after-normal-rematerialization', 'after-four-consumer-gates']]
    external = {**original, 'source_complete_snapshot': descriptors['source_complete_snapshot']}
    return contexts, external, copy.deepcopy(SELECTION), runtime, dict(runtime), dict(runtime)


class FreshContextSuccessor(unittest.TestCase):
    def test_real_publication_pinned_but_success_unset(self):
        self.assertEqual(NS['CELL00_PUBLICATION'], '2106ae104bb98cd3d647a202df069b380e2de5bc')
        self.assertEqual(NS['CELL00_RUNNER_SHA256'], 'ffcc4aff64705a29d9fa94faf44350753d4ba6faf2abbd0c748d634baf363beb')
        self.assertIsNone(NS['CELL00_RESULT_SHA256'])
        self.assertIs(NS['CELL00_ARTIFACTS_REVIEWED'], False)
        self.assertEqual(NS['CELL00_RESULT'].parent.name, 'p25-cell00-four-consumers-attempt008')

    def test_dormant_main_refuses_before_io_or_mutation(self):
        with patch.object(Path, 'mkdir', side_effect=AssertionError('unexpected mutation')), \
             patch.object(Path, 'read_bytes', side_effect=AssertionError('unexpected read')):
            with self.assertRaisesRegex(RuntimeError, 'DORMANT'):
                NS['main']()

    def test_original_compile_record_comes_from_exact_outer(self):
        self.assertEqual(NS['original_compile_record'](OUTER), OUTER['compile_records'][NS['INPUT']])

    def test_changed_original_compile_record_is_rejected(self):
        broken = copy.deepcopy(OUTER)
        broken['records_after_audit'][NS['INPUT']]['object_sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'original compile'):
            NS['original_compile_record'](broken)

    def test_current_inode_changes_do_not_forge_history(self):
        current = copy.deepcopy(OUTER['final_input_snapshot'])
        for row in current['files']:
            row['inode'] += 1
            row['mtime_ns'] += 100
        NS['validate_original_input_window'](OUTER, current, ROWS)
        self.assertNotEqual(current, OUTER['final_input_snapshot'])

    def test_current_input_content_change_is_rejected(self):
        current = copy.deepcopy(OUTER['final_input_snapshot'])
        current['files'][0]['sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'input'):
            NS['validate_original_input_window'](OUTER, current, ROWS)

    def test_old_input_read_window_mutation_is_rejected(self):
        old = copy.deepcopy(OUTER)
        old['input_snapshot_after_compile']['files'][0]['inode'] += 1
        with self.assertRaisesRegex(RuntimeError, 'historical'):
            NS['validate_original_input_window'](old, OUTER['final_input_snapshot'], ROWS)

    def test_normal_phase_is_counted_separately(self):
        workflow, receipt = accounting_fixture()
        NS['validate_normal_accounting'](workflow, receipt, SELECTION, RECOVERY)

    def test_hidden_normal_phase_is_rejected(self):
        workflow, receipt = accounting_fixture()
        workflow['dependency_modules_compiled'] = []
        with self.assertRaisesRegex(RuntimeError, 'normal'):
            NS['validate_normal_accounting'](workflow, receipt, SELECTION, RECOVERY)

    def test_changed_normal_output_is_rejected(self):
        workflow, receipt = accounting_fixture()
        receipt['normal_stages'][0]['object']['sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'object'):
            NS['validate_normal_accounting'](workflow, receipt, SELECTION, RECOVERY)

    def test_available_owner_cannot_also_be_normally_rebuilt(self):
        workflow, receipt = accounting_fixture()
        receipt['available_objects_reused_without_normal'].append(receipt['normal_stages'][0]['module'])
        with self.assertRaisesRegex(RuntimeError, 'available'):
            NS['validate_normal_accounting'](workflow, receipt, SELECTION, RECOVERY)

    def test_exact_gap_tuple_cannot_be_extended(self):
        workflow, receipt = accounting_fixture()
        receipt['historical_archive_gaps'] = copy.deepcopy(receipt['historical_archive_gaps'])
        workflow['historical_archive_gaps'] = receipt['historical_archive_gaps']
        receipt['historical_archive_gaps'][0]['sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'envelope'):
            NS['validate_normal_accounting'](workflow, receipt, SELECTION, RECOVERY)

    def test_recovered_normal_keeps_full_physical_read_window(self):
        workflow, receipt = accounting_fixture()
        stage = receipt['normal_stages'][0]
        stage['input_snapshot_after'] = copy.deepcopy(stage['input_snapshot_after'])
        stage['input_snapshot_after'][0]['inode'] += 1
        with self.assertRaisesRegex(RuntimeError, 'physical'):
            NS['validate_normal_accounting'](workflow, receipt, SELECTION, RECOVERY)

    def test_fresh_context_uses_all_original_runtime_pins(self):
        self.assertEqual(len(NS['validate_fresh_context_records'](*context_fixture())), 4)

    def test_provider_order_change_is_rejected(self):
        args = context_fixture()
        args[2]['external_provider_roots'][1:3] = args[2]['external_provider_roots'][1:3][::-1]
        with self.assertRaisesRegex(RuntimeError, 'provider'):
            NS['validate_fresh_context_records'](*args)

    def test_companion_change_between_new_observations_is_rejected(self):
        args = context_fixture()
        args[0][2]['entries'][0]['companions'][0]['sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'context changed'):
            NS['validate_fresh_context_records'](*args)

    def test_omitted_runtime_pin_is_rejected(self):
        args = context_fixture()
        args[5].pop('/mathlib/lake-manifest.json')
        with self.assertRaisesRegex(RuntimeError, 'runtime pin'):
            NS['validate_fresh_context_records'](*args)

    def test_inherited_lean_and_full_audit_execution_helpers_unchanged(self):
        def functions(path):
            return {n.name: ast.dump(n, include_attributes=False) for n in ast.parse(path.read_text()).body
                    if isinstance(n, ast.FunctionDef)}
        old, new = functions(HERE / 'run_canonical_cell01_v2.py'), functions(DRIVER)
        for name in ['copy_exact', 'source_graphs', 'run_stage', 'recheck_external_context', 'frozen_snapshot']:
            self.assertEqual(old[name], new[name], name)


if __name__ == '__main__':
    unittest.main()
