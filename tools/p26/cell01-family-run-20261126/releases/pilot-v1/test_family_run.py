#!/usr/bin/env python3
"""Synthetic receipt/recovery regressions only; these tests execute no Lean."""
from pathlib import Path
import copy
import importlib.util
import json
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('family_run', HERE / 'family_run.py')
F = importlib.util.module_from_spec(spec)
spec.loader.exec_module(F)


class Fixture:
    module = 'ImbalancedChen.TestOriginalFloorOwner'

    def __init__(self, root):
        self.stage = root / 'stage'
        self.stage.mkdir()
        self.accepted = {}
        self.obj = self.stage / 'objects' / F.relative(self.module)
        self.obj.parent.mkdir(parents=True)
        self.obj.write_bytes(b'fixture-object-not-a-Lean-proof')
        source = self.stage / 'project' / F.relative(self.module, '.lean')
        source.parent.mkdir(parents=True)
        source.write_text('-- Synthetic source; never passed to Lean.\n')
        audit = self.stage / 'audit' / (F.stem(self.module) + '.lean')
        audit.parent.mkdir()
        audit.write_text('-- Synthetic audit; never passed to Lean.\n')
        inputs = F.write(self.stage, self.stage / 'inputs.json', {'synthetic': True})
        self.context = {'module': self.module, 'stage': str(self.stage), 'source': F.fp(source),
            'audit': F.fp(audit), 'inputs': inputs, 'project': str(source.parent.parent),
            'objects': str(self.stage / 'objects'), 'LEAN_PATH': str(self.stage / 'objects'),
            'lean_binary': {'path': '/fixture/bin/lean'}, 'leanchecker_binary': {'path': '/fixture/bin/leanchecker'},
            'runtime_trees': [], 'runtime': {'external_modules': []}, 'external_imports': [],
            'project_modules': [self.module], 'module_search_roots': [str(self.stage / 'objects')],
            'new_dependencies': []}
        self.context_pin = F.write(self.stage, self.stage / 'context.json', self.context)
        self.contexts = {self.module: (self.context, self.context_pin)}

    def step(self, mode):
        folder = self.stage / 'attempts/a/steps' / F.stem(self.module) / mode
        folder.mkdir(parents=True)
        run = {'stage': str(self.stage), 'module': self.module, 'stage_context': self.context_pin,
            'inputs': self.context['inputs'], 'project': self.context['project'],
            'LEAN_PATH': self.context['LEAN_PATH'], 'source': self.context['source'], 'audit': self.context['audit'],
            'object_path': str(self.obj), 'lean': '/fixture/bin/lean', 'checker': '/fixture/bin/leanchecker',
            'rss_gib': 1, 'wall_seconds': 10}
        run_pin = F.write(self.stage, folder / 'run.json', run)
        F.V.TARGET = self.module
        prerequisites = F.prerequisite_records(self.module, mode, self.context, self.accepted)
        command = {'module': self.module, 'mode': mode, 'run': run_pin, 'context': self.context_pin,
            'source': self.context['source'], 'audit': self.context['audit'],
            'object_before': None if mode == 'normal' else F.fp(self.obj),
            'input_fingerprints': self.context['inputs'], 'prerequisites': prerequisites,
            'argv': F.V.expected_argv(mode, run), 'cwd': run['project'], 'LEAN_PATH': run['LEAN_PATH'],
            'wall_limit_seconds': 10}
        command_pin = F.write(self.stage, folder / 'command.json', command)
        log = folder / 'output.log'
        if mode == 'owned':
            name = self.module + '.test'
            items = [('IMPORTS', [self.module]), ('INVENTORY', {'module': self.module,
                     'environment': [name], 'serialized': [name]}),
                     ('DECL', {'module': self.module, 'name': name, 'type': 'True',
                      'unsafe': False, 'partial': False, 'axiom': False, 'axioms': []}),
                     ('COMPLETE', {'module': self.module, 'count': 1})]
            log.write_text(''.join('P26_GEOMETRY01_AUDIT_' + key + ' ' + json.dumps(value) + '\n'
                                   for key, value in items))
        else:
            log.write_text('replaying ' + self.module + '\n' if mode == 'kernel' else '')
        log_pin = F.fp(log)
        result = {**command, 'status': 'succeeded', 'exit_code': 0, 'timed_out': False,
                  'error': None, 'command': command_pin, 'log': log_pin}
        result_pin = F.write(self.stage, folder / 'result.json', result)
        check = {'status': 'ALL_FROZEN_BYTES_UNCHANGED', 'context': self.context_pin,
                 'inputs': self.context['inputs'], 'runtime_trees': []}
        before = F.write(self.stage, folder / 'before.json', check)
        after = F.write(self.stage, folder / 'after.json', check)
        seal = {'status': 'succeeded', 'module': self.module, 'mode': mode,
                'source': self.context['source'], 'audit': self.context['audit'], 'object': F.fp(self.obj),
                'object_sidecars': [], 'run': run_pin, 'context': self.context_pin,
                'command': command_pin, 'command_result': result_pin, 'log': log_pin,
                'before': before, 'after': after, 'prerequisites': prerequisites}
        if mode == 'normal':
            seal['printed_axioms'] = []
        elif mode == 'owned':
            inventory = F.OWNED.parse_owned(log.read_text(), self.module)
            seal['owned_declarations'] = F.write(self.stage, folder / 'owned-declarations.json', inventory)
            seal['owned_declaration_count'] = 1
            seal['module_byte_context'] = F.write(self.stage, folder / 'module-byte-context.json',
                F.V.module_byte_context([self.module], self.context['module_search_roots']))
        ref = F.write(self.stage, folder / 'ACCEPTED_STEP.json', seal)
        F.validate_step(self.stage, self.module, mode, ref, self.context, self.context_pin, self.accepted)
        self.accepted[(self.module, mode)] = ref
        return ref

    def scan(self):
        return F.scan_history(self.stage, [self.module], self.contexts)


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='fixture-', dir=HERE)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.fixture = Fixture(self.root)

    def test_complete_valid_prefix_is_reused_and_missing_anchor_restored(self):
        f = self.fixture
        for mode in F.MODES:
            f.step(mode)
        objects_before = F.fp(f.obj)
        expected = dict(f.accepted)
        self.assertEqual(f.scan(), expected)
        (f.stage / 'accepted' / F.stem(f.module) / 'normal.json').unlink()
        self.assertEqual(f.scan(), expected)
        self.assertEqual(F.fp(f.obj), objects_before)

    def test_changed_object_is_restore_obligation(self):
        f = self.fixture
        f.step('normal')
        f.obj.write_bytes(b'changed')
        with self.assertRaisesRegex(RuntimeError, 'RESTORE_EXACT_ACCEPTED_OBJECT'):
            f.scan()

    def test_changed_log_is_not_cache_miss(self):
        f = self.fixture
        ref = f.step('normal')
        Path(F.read(ref['path'])['log']['path']).write_text('changed')
        with self.assertRaises(RuntimeError):
            f.scan()

    def test_successful_raw_result_without_seal_blocks_replay(self):
        f = self.fixture
        ref = f.step('normal')
        Path(ref['path']).unlink()
        with self.assertRaisesRegex(RuntimeError, 'RESTORE_SUCCESS_EVIDENCE_CHAIN'):
            f.scan()

    def test_zero_exit_result_without_status_also_blocks_replay(self):
        f = self.fixture
        ref = f.step('normal')
        path = Path(ref['path']).with_name('result.json')
        result = F.read(path)
        result.pop('status')
        path.write_text(json.dumps(result))
        Path(ref['path']).unlink()
        with self.assertRaisesRegex(RuntimeError, 'RESTORE_SUCCESS_EVIDENCE_CHAIN'):
            f.scan()

    def test_failure_index_retains_lost_acceptance_obligation(self):
        f = self.fixture
        ref = f.step('normal')
        Path(ref['path']).unlink()
        Path(ref['path']).with_name('result.json').unlink()
        F.write(f.stage, f.stage / 'attempts/a/RESULT.json', {'status': 'FAILED_STOPPED',
            'records': [{'module': f.module, 'mode': 'normal', 'receipt': ref}]})
        with self.assertRaises(RuntimeError):
            f.scan()

    def test_unreceipted_object_cannot_be_recompiled(self):
        with self.assertRaisesRegex(RuntimeError, 'UNRECEIPTED_OBJECT'):
            self.fixture.scan()

    def test_kernel_without_accepted_normal_is_rejected(self):
        f = self.fixture
        normal = f.step('normal')
        f.step('kernel')
        Path(normal['path']).unlink()
        Path(normal['path']).with_name('result.json').unlink()
        with self.assertRaisesRegex(RuntimeError, 'ordered prefix'):
            f.scan()

    def test_prerequisite_receipts_are_bound(self):
        f = self.fixture
        f.step('normal')
        ref = f.step('kernel')
        seal = F.read(ref['path'])
        seal['prerequisites'] = []
        Path(ref['path']).write_text(json.dumps(seal))
        with self.assertRaisesRegex(RuntimeError, 'prerequisite seals'):
            f.scan()

    def test_forbidden_owned_axiom_is_rejected(self):
        f = self.fixture
        f.step('normal'); f.step('kernel')
        ref = f.step('owned')
        text = Path(F.read(ref['path'])['log']['path']).read_text().replace('"axioms": []', '"axioms": ["sorryAx"]')
        with self.assertRaisesRegex(RuntimeError, 'Forbidden owned transitive axiom'):
            F.OWNED.parse_owned(text, f.module)

    def test_truncated_owned_type_is_rejected(self):
        f = self.fixture
        f.step('normal'); f.step('kernel')
        ref = f.step('owned')
        text = Path(F.read(ref['path'])['log']['path']).read_text().replace('"type": "True"', '"type": "⋯"')
        with self.assertRaisesRegex(RuntimeError, 'Truncated owned type'):
            F.OWNED.parse_owned(text, f.module)

    def test_row001_full_receipt_registration_is_forbidden(self):
        provider = self.root / 'provider'
        provider.mkdir()
        path = provider / 'receipt.json'
        path.write_text('{}')
        store = F.E.EvidenceStore(self.fixture.stage, [provider])
        ref = {**F.fp(path), 'path': str(F.E.ROW001_ORIGIN / 'verification/owned-result.json')}
        with self.assertRaisesRegex(RuntimeError, 'ROW001_REMOTE_ONLY'):
            store.register(ref, path)

    def test_no_implicit_fallback_to_original_historical_path(self):
        provider = self.root / 'provider'
        provider.mkdir()
        path = provider / 'receipt.json'
        path.write_text('{}')
        store = F.E.EvidenceStore(self.fixture.stage, [provider])
        with self.assertRaisesRegex(RuntimeError, 'UNRESOLVED_ORIGINAL_EVIDENCE'):
            store.resolve(F.fp(path))

    def test_same_module_source_conflict_is_rejected_before_provenance(self):
        provider = self.root / 'provider'
        provider.mkdir()
        src, obj = provider / 's.lean', provider / 's.olean'
        src.write_text('wrong bytes'); obj.write_bytes(b'object')
        supplier = 'ImbalancedChen.Supplier'
        rows = {self.fixture.module: {'project_imports': [supplier]},
                supplier: {'project_imports': [], 'bytes': 1, 'sha256': '0' * 64}}
        join = {'schema': 'p26_family_owner_join_v1', 'module': self.fixture.module,
                'read_roots': [str(provider)], 'suppliers': [{'module': supplier,
                'source': F.fp(src), 'object': F.fp(obj), 'sidecars': [], 'kind': 'canonical'}]}
        with self.assertRaisesRegex(RuntimeError, 'Same-name source conflict'):
            F.validate_join(self.fixture.stage, join, self.fixture.module, rows, [self.fixture.module], {}, F.E.Frozen())


class SelectedPrefixTests(unittest.TestCase):
    def prefix(self):
        ref = {'path': '/fixture/result.json', 'bytes': 1, 'sha256': '0' * 64}
        return {'status': 'BUDGET_PAUSE', 'selected_ordinals': list(range(98, 144)),
            'completed_rows': list(range(98, 107)), 'remaining_ordinals': list(range(107, 144)),
            'frozen_inputs_unchanged': True, 'batch_complete': False,
            'records': [{'module': 'ImbalancedChen.P2OriginalSaving19Cell01Row%03dFinite' % n,
                         'mode': mode, 'receipt': dict(ref), 'status': 'succeeded'}
                        for n in range(98, 107) for mode in F.MODES]}

    def test_prefix_has_exact_three_chains_for_106(self):
        self.assertEqual(len(F.index_records(self.prefix(), 'ImbalancedChen.P2OriginalSaving19Cell01Row106Finite')), 3)

    def test_prefix_cannot_credit_tail_107(self):
        with self.assertRaises(RuntimeError):
            F.index_records(self.prefix(), 'ImbalancedChen.P2OriginalSaving19Cell01Row107Finite')

    def test_missing_owned_in_prefix_is_rejected(self):
        value = self.prefix(); value['records'].pop()
        with self.assertRaises(RuntimeError):
            F.index_records(value, 'ImbalancedChen.P2OriginalSaving19Cell01Row098Finite')

    def test_success_claim_cannot_cover_shorter_prefix(self):
        value = self.prefix(); value.update(status='succeeded', batch_complete=True)
        with self.assertRaises(RuntimeError):
            F.index_records(value, 'ImbalancedChen.P2OriginalSaving19Cell01Row098Finite')


if __name__ == '__main__':
    unittest.main(verbosity=2)
