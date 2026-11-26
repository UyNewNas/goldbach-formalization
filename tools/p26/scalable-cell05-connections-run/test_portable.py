#!/usr/bin/env python3
"""Synthetic relocation regressions; these bytes carry no Lean acceptance."""
from pathlib import Path, PurePosixPath as P
import copy
import json
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from evidence_io import EvidenceView, archive_bytes, pin, require, write_archive
from portable_receipts import MODES, PACKAGES, expected_argv, target_paths, validate_success
from receipt_support import parse_owned
from supplier_capsule import load_plan, row_mapping


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


class HistoricalFixture:
    def __init__(self, count=2):
        self.files = {}
        self.tool_rel = 'tools/p26/synthetic-historical-workflow'
        self.stage = P('/historical-host/immutable-stage')
        self.modules = [f'ImbalancedChen.SyntheticRelocation{i}' for i in range(count)]
        self.old = 'ImbalancedChen.SyntheticOldSupplier'
        self.context = {'schema': 'cell05_complete_context_v2', 'stage': str(self.stage),
                        'cwd': str(self.stage / 'project'), 'objects': str(self.stage / 'objects'),
                        'supplier_project': '/historical-host/provider/project', 'supplier_objects': '/historical-host/provider/objects',
                        'mathlib': '/historical-host/mathlib', 'mathlib_objects': '/historical-host/mathlib/.lake/build/lib/lean',
                        'mathlib_dependency_parent': '/historical-host/packages',
                        'mathlib_package_object_roots': [f'/historical-host/packages/{name}/.lake/build/lib/lean' for name in PACKAGES],
                        'rss_limit_bytes': 6 * 1024**3, 'wall_limit_seconds': 900,
                        'old_supplier_proof_commands': 0, 'cloud_source_generation': False,
                        'full_supplier_kernel_closed_in_combined_evidence': True}
        runtime = {key: self.put('/historical-host/toolchain/bin/' + name, ('SYNTHETIC ' + name).encode())
                   for key, name in [('lean_binary', 'lean'), ('leanchecker_binary', 'leanchecker')]}
        runtime.update(lean_version='SYNTHETIC NEVER EXECUTED', mathlib_commit='0' * 40)
        self.context['runtime'] = runtime
        roots = [self.context['objects'], *self.context['mathlib_package_object_roots'], self.context['mathlib_objects']]
        self.context['environment'] = {'LEAN_PATH': ':'.join(roots), 'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1',
                                       'LEAN_SYSROOT': '/historical-host/toolchain', 'PATH': '/synthetic',
                                       'LD_LIBRARY_PATH': None, 'LEAN_OPTS': None, 'LEAN_SRC_PATH': None}
        old_source = self.put(self.stage / 'project' / (self.old.replace('.', '/') + '.lean'), b'SYNTHETIC OLD SOURCE')
        old_object = self.put(self.stage / 'objects' / (self.old.replace('.', '/') + '.olean'), b'SYNTHETIC OLD OBJECT')
        self.context['suppliers'] = [{'module': self.old, 'source': old_source, 'object': old_object, 'project_imports': []}]
        frozen, targets = [old_source, old_object], []
        for i, module in enumerate(self.modules):
            paths = target_paths(self.context, module, self.tool_rel)
            source = self.put(paths['source'], ('SYNTHETIC SOURCE ' + module).encode())
            audit = self.put(paths['audit'], ('SYNTHETIC AUDIT ' + module).encode())
            self.put(paths['object'], ('SYNTHETIC OBJECT ' + module).encode())
            dependencies = [self.old] + self.modules[:i]
            targets.append({'module': module, 'source': source, 'audit': audit,
                            'project_imports': [dependencies[-1]], 'transitive_dependencies': sorted(dependencies)})
            frozen.extend([source, audit])
        self.context.update(targets=targets, frozen_inputs=frozen)
        self.run_path = self.stage / 'verification/attempt_original/RUN.json'
        self.put(self.run_path, encoded({'schema': 'cell05_complete_run_v2', 'attempt': 'attempt_original', 'context': self.context}))
        self.success_path = self.run_path.with_name('SUCCESS.json')
        self.records = []
        for module in self.modules:
            for mode in MODES:
                self.make_step(module, mode)
        self.update_success()

    def put(self, path, data):
        self.files[str(path)] = data
        return {'path': str(path), **pin(data)}

    def fp(self, path):
        return {'path': str(path), **pin(self.files[str(path)])}

    def make_step(self, module, mode):
        folder = self.run_path.parent / module.split('.')[-1]
        command_path, result_path, seal_path = [folder / (mode + suffix) for suffix in ('-command.json', '-result.json', '-accepted.json')]
        paths = target_paths(self.context, module, self.tool_rel)
        target = next(row for row in self.context['targets'] if row['module'] == module)
        command = {'schema': 'cell05_step_command_v2', 'run': self.fp(self.run_path), 'module': module, 'mode': mode,
                   'argv': expected_argv(self.context, module, mode, self.tool_rel), 'cwd': self.context['cwd'],
                   'environment': self.context['environment'], 'source': self.fp(paths['source']),
                   'audit_source': self.fp(paths['audit']) if mode == 'owned' else None,
                   'dependency_objects': {m: self.fp(self.stage / 'objects' / (m.replace('.', '/') + '.olean'))
                                          for m in target['transitive_dependencies']},
                   'object_before': None if mode == 'normal' else self.fp(paths['object'])}
        self.put(command_path, encoded(command))
        if mode == 'kernel':
            log = 'replaying ' + module + '\n'
        elif mode == 'normal':
            log = 'SYNTHETIC normal; not Lean\n'
        else:
            name = module + '.synthetic'
            parts = [('P26_GEOMETRY01_AUDIT_INVENTORY ', {'module': module, 'environment': [name], 'serialized': [name]}),
                     ('P26_GEOMETRY01_AUDIT_DECL ', {'module': module, 'name': name, 'type': 'True', 'unsafe': False,
                                                    'partial': False, 'axiom': False, 'axioms': []}),
                     ('P26_GEOMETRY01_AUDIT_COMPLETE ', {'module': module, 'count': 1})]
            log = ''.join(marker + json.dumps(value) + '\n' for marker, value in parts)
        log_path = folder / (mode + '.log')
        self.put(log_path, log.encode())
        result = {'schema': 'cell05_step_result_v2', 'run': self.fp(self.run_path), 'command': self.fp(command_path),
                  'module': module, 'mode': mode, 'status': 'succeeded', 'exit_code': 0, 'termination_reason': None,
                  'source': command['source'], 'audit_source': command['audit_source'], 'dependency_objects': command['dependency_objects'],
                  'object': self.fp(paths['object']), 'log': self.fp(log_path), 'elapsed_seconds': 0.1, 'peak_rss_bytes': 1}
        if mode == 'normal':
            result['printed_axioms'] = []
        elif mode == 'owned':
            owned = parse_owned(log, module)
            result['owned_declarations'] = self.put(folder / 'owned-declarations.json', encoded(owned))
            result['owned_declaration_count'] = owned['owned_declaration_count']
        self.put(result_path, encoded(result))
        seal = {'schema': 'cell05_step_accepted_v2', 'status': 'accepted', 'module': module, 'mode': mode,
                'run': self.fp(self.run_path), 'command': self.fp(command_path), 'result': self.fp(result_path), 'object': result['object']}
        identity = self.put(seal_path, encoded(seal))
        self.records.append({'module': module, 'mode': mode, 'accepted': identity, 'disposition': 'executed'})

    def update_success(self):
        self.success = {'schema': 'cell05_complete_success_v2', 'status': 'succeeded', 'run': self.fp(self.run_path),
                        'context': self.context, 'records': self.records, 'accepted_targets': len(self.modules),
                        'accepted_steps': len(self.records), 'newly_executed_steps': len(self.records), 'reused_steps': 0,
                        'frozen_inputs_unchanged': True, 'whole_geometry_decoded': False, 'P2_6_complete': False}
        self.success_identity = self.put(self.success_path, encoded(self.success))

    def reseal(self, index, command_change=None, result_change=None):
        record = self.records[index]
        seal_path = record['accepted']['path']
        seal = json.loads(self.files[seal_path])
        command_path, result_path = seal['command']['path'], seal['result']['path']
        command, result = json.loads(self.files[command_path]), json.loads(self.files[result_path])
        if command_change:
            command_change(command)
        self.put(command_path, encoded(command))
        result['command'] = self.fp(command_path)
        if result_change:
            result_change(result)
        self.put(result_path, encoded(result))
        seal['command'], seal['result'] = self.fp(command_path), self.fp(result_path)
        record['accepted'] = self.put(seal_path, encoded(seal))
        self.update_success()

    def view(self):
        view = EvidenceView()
        for old, data in self.files.items():
            view.add(old, data, {'kind': 'synthetic-relocated-bytes', 'blob': pin(data)['sha256']})
        return view

    def validate(self, view=None):
        return validate_success(view or self.view(), self.success_identity, self.context, self.tool_rel, len(self.modules))


class PortableTests(unittest.TestCase):
    def test_exact_historical_bytes_validate_without_original_host_paths(self):
        fixture = HistoricalFixture()
        self.assertFalse(Path('/historical-host/immutable-stage').exists())
        before = copy.deepcopy(fixture.files)
        checked = fixture.validate()
        self.assertEqual((checked['accepted_steps'], checked['owned_declaration_count']), (6, 2))
        self.assertEqual(fixture.files, before)

    def test_wrong_old_absolute_path_has_no_prefix_fallback(self):
        fixture = HistoricalFixture()
        view = fixture.view()
        old = str(target_paths(fixture.context, fixture.modules[0], fixture.tool_rel)['source'])
        data = view.values.pop(old)
        view.add(old.replace('/historical-host/', '/different-host/'), data, {'kind': 'wrong-alias'})
        with self.assertRaisesRegex(RuntimeError, 'Unmapped'):
            fixture.validate(view)

    def test_semantic_tampering_rejected_even_with_resealed_hashes(self):
        cases = [('module', lambda c: c.update(module='ImbalancedChen.Other')),
                 ('mode', lambda c: c.update(mode='normal')),
                 ('argv', lambda c: c.update(argv=[c['argv'][0], '--verbose', 'ImbalancedChen.Other'])),
                 ('cwd', lambda c: c.update(cwd='/different/project')),
                 ('LEAN_PATH', lambda c: c['environment'].update(LEAN_PATH='/different/runtime')),
                 ('object_before', lambda c: c.update(object_before=None)),
                 ('source', lambda c: c['source'].update(path='/different/source.lean')),
                 ('dependencies', lambda c: c.update(dependency_objects={}))]
        for name, change in cases:
            with self.subTest(name=name):
                fixture = HistoricalFixture()
                fixture.reseal(1, command_change=change)
                with self.assertRaises(RuntimeError):
                    fixture.validate()

    def test_missing_log_result_object_or_owned_inventory_blocks_reuse(self):
        for suffix in ['kernel.log', 'normal-result.json', '.olean', 'owned-declarations.json']:
            with self.subTest(suffix=suffix):
                fixture = HistoricalFixture()
                name = next(name for name in fixture.files if name.endswith(suffix))
                del fixture.files[name]
                with self.assertRaises(RuntimeError):
                    fixture.validate()

    def test_three_steps_cannot_accept_another_object(self):
        fixture = HistoricalFixture()
        fixture.reseal(1, result_change=lambda r: r['object'].update(sha256='f' * 64))
        with self.assertRaises(RuntimeError):
            fixture.validate()

    def test_shared_old_supplier_bytes_must_match(self):
        fixture = HistoricalFixture()
        old = str(fixture.stage / 'objects' / (fixture.old.replace('.', '/') + '.olean'))
        fixture.files[old] += b'CHANGED'
        with self.assertRaises(RuntimeError):
            fixture.validate()

    def test_regular_archive_readback_and_duplicate_or_extra_members(self):
        with tempfile.TemporaryDirectory(dir='/dev/shm') as temp:
            root = Path(temp)
            files = {'one': b'same bytes', 'two': b'same bytes'}
            manifest = {'members': [{'member': name, **pin(data)} for name, data in sorted(files.items())]}
            output = root / 'capsule.tar.xz'
            write_archive(output, files, manifest)
            got = archive_bytes(output)
            self.assertEqual(got['one'], got['two'])
            with self.assertRaises(RuntimeError):
                write_archive(output, files, manifest)

    def test_real_metadata_derives_only_exact_necessary_mapping(self):
        here = Path(__file__).absolute().parent
        mappings = row_mapping(here, load_plan(here))
        self.assertEqual(len(mappings), 496)
        self.assertEqual(sum(r['resolved']['kind'] == 'fields_archive_member' for r in mappings), 154)
        self.assertEqual(sum(r['resolved']['kind'] == 'old_supplier' for r in mappings), 60)
        self.assertEqual(len({r['resolved']['member'] for r in mappings if r['resolved']['kind'] == 'blob'}), 265)
        object_rows = [r for r in mappings if r['original']['path'].endswith('.olean') and r['resolved']['kind'] == 'blob']
        self.assertEqual(len(object_rows), 15)


if __name__ == '__main__':
    unittest.main(verbosity=2)
