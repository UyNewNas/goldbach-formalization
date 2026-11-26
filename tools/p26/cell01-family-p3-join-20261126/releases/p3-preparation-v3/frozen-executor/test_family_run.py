#!/usr/bin/env python3
"""Synthetic receipt/recovery regressions only; these tests execute no Lean."""
from pathlib import Path
import copy
import importlib.util
import json
import tempfile
import unittest
from unittest import mock

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
            'object_path': str(self.obj), 'lean': self.context['lean_binary']['path'],
            'checker': self.context['leanchecker_binary']['path'],
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

    def test_three_step_pilot_cannot_be_labeled_full_family_success(self):
        value = {'status': 'PASS_CELL01_ORIGINAL_FLOOR_FAMILY_11', 'accepted_steps': 3,
                 'accepted_owners': 1, 'P2_6_complete_claimed': False,
                 'records': [{'module': F.INTERFACE, 'mode': mode,
                              'receipt': {'path': '/fixture/result.json', 'bytes': 1, 'sha256': '0' * 64}}
                             for mode in F.MODES]}
        with self.assertRaisesRegex(RuntimeError, 'all 33 accepted steps'):
            F.index_records(value, F.INTERFACE)


class HistoricalFiniteTests(unittest.TestCase):
    """The real finite batch schema uses raw result receipts and inherits RUN fields."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='finite-', dir=HERE)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.provider = self.root / 'provider'
        self.provider.mkdir()
        self.stage = self.root / 'new-stage'
        self.module = 'ImbalancedChen.P2OriginalSaving19Cell01Row002Finite'
        self.rows = {self.module: {'project_imports': []}}
        self.files = []
        def body(name, value):
            path = self.provider / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(value))
            self.files.append(path)
            return F.fp(path)
        self.body = body
        source = self.provider / 'project' / F.relative(self.module, '.lean')
        source.parent.mkdir(parents=True)
        source.write_text('-- Synthetic finite fixture.\n')
        obj = self.provider / 'objects' / F.relative(self.module)
        obj.parent.mkdir(parents=True)
        obj.write_bytes(b'synthetic-object')
        audit = self.provider / 'audit.lean'
        audit.write_text('-- Synthetic owned audit.\n')
        lean, checker = self.provider / 'lean', self.provider / 'leanchecker'
        lean.write_bytes(b'synthetic-lean'); checker.write_bytes(b'synthetic-checker')
        self.files += [source, obj, audit, lean, checker]
        self.source, self.obj, self.audit = F.fp(source), F.fp(obj), F.fp(audit)
        self.runtime = {'lean_binary': F.fp(lean), 'leanchecker_binary': F.fp(checker)}
        input_ref = body('INPUT_FINGERPRINTS.json', {'files': [], 'cloud_source_generation': False})
        run = {**self.runtime, 'input_fingerprints': input_ref, 'cwd': str(source.parent.parent),
               'LEAN_PATH': str(obj.parent.parent), 'runtime_context_sha256': 'f' * 64,
               'selected_ordinals': [2], 'accepted_supplier_count': 399, 'suppliers_recompiled': False}
        run_ref = body('RUN.json', run)
        records = []
        for mode in F.MODES:
            flags = ['-j1', '-M1024', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
            argv = ([str(checker), '--verbose', self.module] if mode == 'kernel' else
                    [str(lean), *flags, '-o', str(obj), self.module.replace('.', '/') + '.lean'] if mode == 'normal' else
                    [str(lean), *flags, str(audit)])
            command = {**run, 'module': self.module, 'mode': mode, 'argv': argv, 'source': self.source,
                       'object_before': None if mode == 'normal' else self.obj,
                       'audit_source': self.audit if mode == 'owned' else None}
            command_ref = body(mode + '-command.json', command)
            log = self.provider / (mode + '.log')
            if mode == 'owned':
                name = self.module + '.test'
                payloads = [('IMPORTS', [self.module]), ('INVENTORY', {'module': self.module,
                            'serialized': [name], 'environment': [name]}),
                            ('DECL', {'module': self.module, 'name': name, 'type': 'True',
                             'unsafe': False, 'partial': False, 'axiom': False, 'axioms': []}),
                            ('COMPLETE', {'module': self.module, 'count': 1})]
                log.write_text(''.join('P26_GEOMETRY01_AUDIT_' + key + ' ' + json.dumps(value) + '\n'
                                       for key, value in payloads))
            else:
                log.write_text('replaying ' + self.module + '\n' if mode == 'kernel' else '')
            self.files.append(log)
            result = {**command, 'command': command_ref, 'log': F.fp(log), 'status': 'succeeded',
                      'exit_code': 0, 'object': self.obj}
            if mode == 'owned':
                result['owned_declarations'] = body('owned-declarations.json', F.OWNED.parse_owned(log.read_text(), self.module))
            records.append({'module': self.module, 'mode': mode,
                            'receipt': body(mode + '-result.json', result), 'status': 'succeeded'})
        index_ref = body('SUCCESS.json', {**run, 'status': 'succeeded', 'frozen_inputs_unchanged': True,
                     'batch_complete': True, 'completed_rows': [2], 'records': records})
        self.provenance = {'run': run_ref, 'input': input_ref, 'index': index_ref,
                           'records': [{'mode': r['mode'], 'receipt': r['receipt']} for r in records]}

    def store(self):
        store = F.E.EvidenceStore(self.stage, [self.provider])
        for path in self.files:
            store.register(F.fp(path), path)
        return store

    def test_actual_raw_finite_receipt_shape_is_accepted(self):
        result, _ = F.old_chain(self.provenance, self.module, self.source, self.obj,
                               self.runtime, self.store(), self.rows)
        self.assertEqual(result['status'], 'EXACT_EXISTING_THREE_MODE_CHAIN_RECHECKED')

    def test_source_manifest_status_does_not_replace_three_receipts(self):
        wrong = dict(self.provenance, records=[])
        with self.assertRaisesRegex(RuntimeError, 'immutable acceptance index'):
            F.old_chain(wrong, self.module, self.source, self.obj, self.runtime, self.store(), self.rows)

    def test_different_live_object_is_not_accepted_from_module_name(self):
        wrong = {**self.obj, 'sha256': '0' * 64}
        with self.assertRaisesRegex(RuntimeError, 'identity conflict'):
            F.old_chain(self.provenance, self.module, self.source, wrong, self.runtime, self.store(), self.rows)

    def test_compiler_hash_must_match_current_frozen_runtime(self):
        wrong = {**self.runtime, 'lean_binary': {**self.runtime['lean_binary'], 'sha256': '0' * 64}}
        with self.assertRaisesRegex(RuntimeError, 'compiler/checker bytes differ'):
            F.old_chain(self.provenance, self.module, self.source, self.obj, wrong, self.store(), self.rows)


class SameHostAndFailureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='host-', dir=HERE)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_same_host_body_resolves_without_relocation_and_changed_bytes_fail(self):
        origin = self.root / 'original'
        path = origin / 'verification/result.json'
        path.parent.mkdir(parents=True)
        path.write_text('{}')
        with mock.patch.object(F.E, 'ROW001_ORIGIN', origin):
            store = F.Row001InPlaceStore(self.root / 'new-stage', [origin])
            ref = F.fp(path)
            self.assertEqual(store.resolve(ref), path)
            path.write_text('{"changed": true}')
            with self.assertRaises(RuntimeError):
                store.resolve(ref)

    def test_same_host_mode_still_forbids_transferring_raw_body(self):
        origin = self.root / 'original'
        origin.mkdir()
        transferred = self.root / 'transferred'
        transferred.mkdir()
        path = transferred / 'result.json'
        path.write_text('{}')
        with mock.patch.object(F.E, 'ROW001_ORIGIN', origin):
            store = F.Row001InPlaceStore(self.root / 'new-stage', [origin, transferred])
            ref = {**F.fp(path), 'path': str(origin / 'verification/result.json')}
            with self.assertRaisesRegex(RuntimeError, 'ROW001_REMOTE_ONLY'):
                store.register(ref, path)

    def test_same_host_mode_never_opens_completed_archive(self):
        origin = self.root / 'original'
        origin.mkdir()
        path = origin / 'completed.tar.xz'
        path.write_bytes(b'not an archive')
        with mock.patch.object(F.E, 'ROW001_ORIGIN', origin):
            store = F.Row001InPlaceStore(self.root / 'new-stage', [origin])
            with self.assertRaisesRegex(RuntimeError, 'original same-host row001 receipt bodies'):
                store.resolve(F.fp(path))

    def test_known_failed_output_is_preserved_and_never_accepted(self):
        f = Fixture(self.root)
        folder = f.stage / 'attempts/failure/steps' / F.stem(f.module) / 'normal'
        F.write(f.stage, folder / 'result.json', {'module': f.module, 'mode': 'normal',
                'status': 'failed', 'exit_code': 1, 'object_before': None})
        before = F.fp(f.obj)
        saved = F.preserve_failed_normal(f.stage, f.stage / 'attempts/failure', f.module, folder, f.obj)
        self.assertFalse(f.obj.exists())
        self.assertTrue(F.same(saved[0]['preserved'], before))
        self.assertEqual(f.scan(), {})

    def test_successful_output_is_never_quarantined_for_replay(self):
        f = Fixture(self.root)
        folder = f.stage / 'attempts/success/steps' / F.stem(f.module) / 'normal'
        F.write(f.stage, folder / 'result.json', {'module': f.module, 'mode': 'normal',
                'status': 'succeeded', 'exit_code': 0, 'object_before': None})
        with self.assertRaisesRegex(RuntimeError, 'cannot touch successful evidence'):
            F.preserve_failed_normal(f.stage, f.stage / 'attempts/success', f.module, folder, f.obj)
        self.assertTrue(f.obj.exists())


class ImportedPilotTests(unittest.TestCase):
    """Synthetic direct and relocated receipts exercise the real import validator, not Lean."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='import-', dir=HERE)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        donor_parent = self.root / 'donor'
        donor_parent.mkdir()
        class PilotFixture(Fixture):
            module = F.INTERFACE
        donor = PilotFixture(donor_parent)
        self.donor = donor
        code_root = next((path for path in (HERE / 'releases/pilot-v1', HERE.parent / 'pilot-v1')
                          if (path / 'CODE_MANIFEST.json').exists()), None)
        self.assertIsNotNone(code_root, 'The frozen pilot-v1 reference must be available beside the v2 release')
        code_ref = F.fp(code_root / 'CODE_MANIFEST.json')
        code_files = [code_root / row['member'] for row in F.read(code_ref['path'])['files']]
        input_path = Path(donor.context['inputs']['path'])
        input_path.write_text(json.dumps({'files': [code_ref, *map(F.fp, code_files)]}))
        donor.context['inputs'] = F.fp(input_path)
        binaries = donor.stage / 'bin'
        binaries.mkdir()
        lean, checker = binaries / 'lean', binaries / 'leanchecker'
        lean.write_bytes(b'fixture lean'); checker.write_bytes(b'fixture checker')
        runtime = {'lean_binary': F.fp(lean), 'leanchecker_binary': F.fp(checker), 'external_modules': []}
        donor.context.update(runtime=runtime, lean_binary=F.fp(lean), leanchecker_binary=F.fp(checker),
            schema='p26_family_owner_context_v1', source_archive=F.SOURCE_ARCHIVE,
            new_owner_count=11, P2_6_complete_claimed=False)
        context_path = Path(donor.context_pin['path'])
        context_path.write_text(json.dumps(donor.context))
        donor.context_pin = F.fp(context_path)
        for mode in F.MODES:
            donor.step(mode)
        records = [{'module': F.INTERFACE, 'mode': mode, 'receipt': donor.accepted[(F.INTERFACE, mode)]}
                   for mode in F.MODES]
        index = F.write(donor.stage, donor.stage / 'RESULT.json', {'status': 'PAUSED_ACCEPTED_PREFIX',
                        'accepted_steps': 3, 'accepted_owners': 1, 'P2_6_complete_claimed': False, 'records': records})
        normal = F.read(records[0]['receipt']['path'])
        provenance = {'run': normal['run'], 'input': donor.context['inputs'], 'index': index,
                      'code_manifest': code_ref,
                      'records': [{'mode': r['mode'], 'receipt': r['receipt']} for r in records]}
        self.stage = self.root / 'new-stage'
        current_source = self.stage / 'project' / F.relative(F.INTERFACE, '.lean')
        current_audit = self.stage / 'audit' / (F.stem(F.INTERFACE) + '.lean')
        for current, origin in [(current_source, donor.context['source']), (current_audit, donor.context['audit'])]:
            current.parent.mkdir(parents=True, exist_ok=True)
            current.write_bytes(Path(origin['path']).read_bytes())
        provider = self.root / 'metadata'
        provider.mkdir()
        catalog_path = provider / 'source-catalog.json'
        catalog_path.write_text(json.dumps({'project_source_closure': [{'module': F.INTERFACE, 'project_imports': []}]}))
        self.catalog_pin = F.fp(catalog_path)
        self.context = {**donor.context, 'stage': str(self.stage), 'project': str(self.stage / 'project'),
            'objects': str(self.stage / 'objects'), 'source': F.fp(current_source), 'audit': F.fp(current_audit),
            'module_search_roots': [str(self.stage / 'objects')], 'source_manifest': self.catalog_pin}
        self.context_pin = F.write(self.stage, self.stage / 'context.json', self.context)
        bindings = [{'original': F.fp(path), 'current_path': str(path)}
                    for path in [*sorted(donor.stage.rglob('*')), code_root / 'CODE_MANIFEST.json', *code_files]
                    if path.is_file()]
        self.join = {'schema': 'p26_family_owner_join_v1', 'module': F.INTERFACE,
            'read_roots': [str(donor.stage), str(code_root)], 'bindings': bindings, 'suppliers': [],
            'accepted_owner': {'module': F.INTERFACE, 'source': donor.context['source'],
             'audit': donor.context['audit'], 'object': F.fp(donor.obj), 'sidecars': [], 'provenance': provenance}}
        self.join_path = provider / 'JOIN.json'
        self.join_path.write_text(json.dumps(self.join))
        # Only the catalog checksum is replaced for the small synthetic graph.
        # Original code release pins and every command/receipt validator remain real.
        self.patch = mock.patch.object(F, 'SOURCE_MANIFEST', self.catalog_pin)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def run_import(self):
        return F.import_interface(self.stage, self.context, self.context_pin, self.join_path, F.E.Frozen())

    def test_imported_complete_pilot_is_reused_and_missing_anchor_restored_without_Lean(self):
        with mock.patch.object(F.SHARED, 'run_command', side_effect=AssertionError('No Lean permitted')) as call:
            self.run_import()
            contexts = {F.INTERFACE: (self.context, self.context_pin)}
            accepted = F.scan_history(self.stage, [F.INTERFACE], contexts)
            self.assertEqual(len(accepted), 3)
            obj = self.stage / 'objects' / F.relative(F.INTERFACE)
            object_pin = F.fp(obj)
            (self.stage / 'accepted' / F.FILENAME_INTERFACE / 'kernel.json').unlink()
            Path(accepted[(F.INTERFACE, 'kernel')]['path']).unlink()
            self.run_import()
            self.assertEqual(F.scan_history(self.stage, [F.INTERFACE], contexts), accepted)
            self.assertEqual(F.fp(obj), object_pin)
            call.assert_not_called()

    def test_changed_original_log_cannot_be_imported_or_replayed(self):
        seal = F.read(self.donor.accepted[(F.INTERFACE, 'normal')]['path'])
        Path(seal['log']['path']).write_text('changed after acceptance')
        with self.assertRaises(RuntimeError):
            self.run_import()
        self.assertFalse((self.stage / 'objects' / F.relative(F.INTERFACE)).exists())

    def test_import_rejects_unreviewed_original_code_before_object_installation(self):
        self.join['accepted_owner']['provenance']['code_manifest'] = {**self.join['accepted_owner']['provenance']['code_manifest'],
                                                                    'sha256': '0' * 64}
        self.join_path.write_text(json.dumps(self.join))
        with self.assertRaisesRegex(RuntimeError, 'frozen reviewed pilot-v1 code'):
            self.run_import()
        self.assertFalse((self.stage / 'objects' / F.relative(F.INTERFACE)).exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
