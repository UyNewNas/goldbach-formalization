#!/usr/bin/env python3
"""Synthetic tests for the new one-owner boundary. No fixture is Lean evidence."""
from pathlib import Path
import copy
import json
import os
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
import receipt_checks as C
import origin_join as O
import stage_entry as S
from boundary import BOUNDARY, TARGET, TOOL_REL
from export_shape import select_new_evidence
from runtime_compat import stat_identity


def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(data if isinstance(data, str) else json.dumps(data, indent=2) + '\n')


class ShapeFixture:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='synthetic-shape-', dir=Path(__file__).absolute().parent)
        self.base = Path(self.temp.name)
        self.stage, self.origin = self.base / 'repair', self.base / 'original14'
        self.here = self.stage / TOOL_REL
        self.project, self.objects = self.stage / 'project', self.stage / 'objects'
        self.provider = self.base / 'provider88'
        self.fields = self.base / 'original-fields73'
        for path in (self.here, self.origin, self.fields, self.provider / 'project', self.provider / 'objects'):
            path.mkdir(parents=True)
        self.boundary = copy.deepcopy(BOUNDARY)
        self.boundary.update(original_stage=str(self.origin), original_fields_stage=str(self.fields),
                             supplier_project=str(self.provider / 'project'), supplier_objects=str(self.provider / 'objects'))
        modules = BOUNDARY['expected_old_dependency_modules'] + [f'ImbalancedChen.SyntheticUnused{i:02d}' for i in range(46)]
        suppliers, frozen = [], []
        for module in modules:
            relative = module.replace('.', '/')
            source, obj = self.project / (relative + '.lean'), self.objects / (relative + '.olean')
            put(source, '-- SYNTHETIC OLD SUPPLIER: NEVER COMPILED\n')
            put(obj, 'SYNTHETIC OLD OBJECT: NOT LEAN EVIDENCE\n')
            suppliers.append({'module': module, 'source': C.fp(source), 'object': C.fp(obj)})
            frozen += [C.fp(source), C.fp(obj)]
        self.paths = C.target_paths({'stage': str(self.stage)}, TARGET)
        put(self.paths['source'], '-- SYNTHETIC REPAIR: NOT A PROOF\n')
        put(self.stage / 'sources' / (TARGET.replace('.', '/') + '.lean'), self.paths['source'].read_text())
        put(self.paths['object'], 'SYNTHETIC NEW OBJECT: NOT LEAN EVIDENCE\n')
        put(self.paths['audit'], '-- SYNTHETIC AUDIT\n')
        self.old_marker = self.origin / 'accepted-prefix-unchanged.txt'
        put(self.old_marker, 'SYNTHETIC MARKER FOR PRESERVED ORIGINAL PREFIX\n')
        self.old_pin = C.fp(self.old_marker)
        lean, checker = self.base / 'runtime/bin/lean', self.base / 'runtime/bin/leanchecker'
        put(lean, 'SYNTHETIC NONEXECUTABLE RUNTIME\n')
        put(checker, 'SYNTHETIC NONEXECUTABLE CHECKER\n')
        mathlib = self.base / 'mathlib-objects'
        mathlib.mkdir()
        self.guard_path = self.provider / 'evidence/RUNTIME_GUARD.json'
        put(self.guard_path, {'schema': 'cell05_connections_runtime_guard_v1',
                             'all_selected_bytes_rehashed_before_guard': True,
                             'entries': [{'path': str(lean), 'lstat': stat_identity(lean)}]})
        self.boundary['runtime_guard'] = C.fp(self.guard_path)
        join_path = self.origin / BOUNDARY['original_tool_relative_path'] / 'SUPPLIER_JOIN.json'
        put(join_path, {'new_stage': str(self.origin), 'runtime_guard': C.fp(self.guard_path)})
        self.target = {**copy.deepcopy(BOUNDARY['original_target']),
                       'source': C.fp(self.paths['source']), 'audit': C.fp(self.paths['audit'])}
        self.context = {'schema': 'cell05_shape_repair_context_v1', 'stage': str(self.stage),
                        'origin_stage': str(self.origin), 'cwd': str(self.project), 'objects': str(self.objects),
                        'targets': [self.target], 'suppliers': suppliers,
                        'runtime': {'lean_binary': C.fp(lean), 'leanchecker_binary': C.fp(checker)},
                        'mathlib_package_object_roots': [], 'mathlib_objects': str(mathlib),
                        'environment': {'LEAN_PATH': os.pathsep.join([str(self.objects), str(mathlib)]),
                                        'LEAN_SYSROOT': str(lean.parent.parent), 'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1'},
                        'rss_limit_bytes': 6 * 1024**3, 'wall_limit_seconds': 900,
                        'runtime_guard': C.fp(self.guard_path), 'supplier_join': C.fp(join_path),
                        'old_supplier_proof_commands': 0, 'original_thirteen_owner_proof_commands': 0,
                        'cloud_source_generation': False,
                        'frozen_inputs': frozen + [C.fp(self.paths['source']), C.fp(self.paths['audit']),
                                                  C.fp(self.guard_path), C.fp(join_path), self.old_pin]}
        self.patches = [mock.patch.object(module, 'BOUNDARY', self.boundary) for module in (C, O, S)]
        for patch in self.patches:
            patch.start()
        self.run_root = self.stage / 'verification/synthetic_attempt1'
        self.run = self.run_root / 'RUN.json'
        put(self.run, {'schema': 'cell05_shape_repair_run_v1', 'attempt': 'synthetic_attempt1', 'context': self.context})

    def close(self):
        if self.old_marker.exists():
            if C.fp(self.old_marker) != self.old_pin:
                raise AssertionError('Test unexpectedly modified the original-prefix marker')
        for patch in reversed(self.patches):
            patch.stop()
        self.temp.cleanup()

    def step(self, mode):
        folder = self.run_root / TARGET.split('.')[-1]
        command_path, result_path, seal_path = [folder / (mode + suffix)
                                               for suffix in ('-command.json', '-result.json', '-accepted.json')]
        command = {'schema': 'cell05_shape_repair_step_command_v1', 'run': C.fp(self.run), 'module': TARGET, 'mode': mode,
                   'argv': C.expected_argv(self.context, TARGET, mode), 'cwd': self.context['cwd'],
                   'environment': self.context['environment'], 'source': C.fp(self.paths['source']),
                   'audit_source': C.fp(self.paths['audit']) if mode == 'owned' else None,
                   'dependency_objects': C.dependency_objects(self.context, TARGET),
                   'object_before': None if mode == 'normal' else C.fp(self.paths['object'])}
        put(command_path, command)
        log_path = folder / (mode + '.log')
        if mode == 'owned':
            name = TARGET + '.syntheticDeclaration'
            log = ''.join(marker + json.dumps(value) + '\n' for marker, value in [
                ('P26_GEOMETRY01_AUDIT_IMPORTS ', BOUNDARY['expected_old_dependency_modules'] + [TARGET]),
                ('P26_GEOMETRY01_AUDIT_INVENTORY ', {'module': TARGET, 'environment': [name], 'serialized': [name]}),
                ('P26_GEOMETRY01_AUDIT_DECL ', {'module': TARGET, 'name': name, 'type': 'True',
                    'unsafe': False, 'partial': False, 'axiom': False, 'axioms': []}),
                ('P26_GEOMETRY01_AUDIT_COMPLETE ', {'module': TARGET, 'count': 1})])
        else:
            log = 'replaying ' + TARGET + '\n' if mode == 'kernel' else 'SYNTHETIC NORMAL LOG\n'
        put(log_path, log)
        result = {'schema': 'cell05_shape_repair_step_result_v1', 'run': C.fp(self.run), 'command': C.fp(command_path),
                  'module': TARGET, 'mode': mode, 'status': 'succeeded', 'exit_code': 0, 'termination_reason': None,
                  'source': command['source'], 'audit_source': command['audit_source'],
                  'dependency_objects': command['dependency_objects'], 'object': C.fp(self.paths['object']),
                  'log': C.fp(log_path), 'elapsed_seconds': 0.01, 'peak_rss_bytes': 1}
        if mode == 'normal':
            result['printed_axioms'] = []
        if mode == 'owned':
            owned_path = folder / 'owned-declarations.json'
            put(owned_path, C.parse_target_owned(log, self.context, TARGET))
            result.update(owned_declarations=C.fp(owned_path), owned_declaration_count=1)
        put(result_path, result)
        put(seal_path, {'schema': 'cell05_shape_repair_step_accepted_v1', 'status': 'accepted', 'module': TARGET,
                        'mode': mode, 'run': C.fp(self.run), 'command': C.fp(command_path),
                        'result': C.fp(result_path), 'object': result['object']})
        return seal_path

    def success(self):
        records = [{'module': TARGET, 'mode': mode, 'accepted': C.fp(self.step(mode)), 'disposition': 'executed'}
                   for mode in C.MODES]
        path = self.run_root / 'SUCCESS.json'
        put(path, {'schema': 'cell05_shape_repair_success_v1', 'status': 'succeeded', 'run': C.fp(self.run),
                   'context': self.context, 'records': records, 'accepted_targets': 1, 'accepted_steps': 3,
                   'newly_executed_steps': 3, 'reused_steps': 0, 'frozen_inputs_unchanged': True,
                   'whole_geometry_decoded': False, 'P2_6_complete': False, 'original_thirteen_owners_reexecuted': False})
        return path


class ShapeIsolationTests(unittest.TestCase):
    def setUp(self):
        self.f = ShapeFixture()

    def tearDown(self):
        self.f.close()

    def test_only_fixed_shape_target_and_exact_42_dependencies(self):
        C.require_single_scope(self.f.context)
        wrong = copy.deepcopy(self.f.context)
        wrong['targets'][0]['module'] = 'ImbalancedChen.UnrequestedOwner'
        with self.assertRaisesRegex(ValueError, 'single fixed'):
            C.require_single_scope(wrong)
        wrong = copy.deepcopy(self.f.context)
        wrong['targets'][0]['transitive_dependencies'][-1] = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesHeader'
        with self.assertRaisesRegex(ValueError, '42 old suppliers'):
            C.require_single_scope(wrong)

    def test_owned_requires_43_project_modules(self):
        seal = self.f.step('owned')
        log = seal.with_name('owned.log').read_text()
        C.parse_target_owned(log, self.f.context, TARGET)
        imports = BOUNDARY['expected_old_dependency_modules'] + [TARGET]
        wrong = log.replace(json.dumps(imports), json.dumps(imports[:-1]))
        with self.assertRaisesRegex(ValueError, 'fixed 43'):
            C.parse_target_owned(wrong, self.f.context, TARGET)

    def test_three_step_completion_cannot_claim_14_or_39(self):
        path = self.f.success()
        self.assertEqual(len(C.validate_success(path)[1]), 3)
        value = C.read(path)
        value.update(accepted_targets=13, accepted_steps=39)
        put(path, value)
        with self.assertRaisesRegex(ValueError, 'counts|scope'):
            C.validate_success(path)

    def test_normal_prefix_reuses_exact_seal_and_missing_object_blocks_replay(self):
        seal = self.f.step('normal')
        reusable = {(TARGET, mode): C.prior(self.f.context, TARGET, mode) for mode in C.MODES}
        self.assertEqual(C.require_accepted_prefix(self.f.context, reusable), 1)
        self.assertEqual(reusable[TARGET, 'normal']['accepted'], C.fp(seal))
        self.f.paths['object'].unlink()
        with self.assertRaisesRegex(ValueError, 'restore exact bytes|Restore|missing'):
            C.reject_missing_successful_objects(self.f.stage, [TARGET])

    def test_same_guard_bytes_at_new_path_are_not_a_replacement(self):
        new_guard = self.f.base / 'replacement-guard.json'
        new_guard.write_bytes(self.f.guard_path.read_bytes())
        altered = copy.deepcopy(self.f.context)
        altered['runtime_guard'] = C.fp(new_guard)
        altered['frozen_inputs'].append(C.fp(new_guard))
        with self.assertRaisesRegex(ValueError, 'original runtime guard'):
            C.check_context_inputs(altered)

    def test_changed_source_cannot_reuse_normal_acceptance(self):
        self.f.step('normal')
        self.f.paths['source'].write_text('-- DIFFERENT SYNTHETIC SOURCE\n')
        with self.assertRaisesRegex(ValueError, 'source pin|Frozen context input'):
            C.prior(self.f.context, TARGET, 'normal')

    def test_missing_result_after_command_blocks_ambiguous_replay(self):
        seal = self.f.step('kernel')
        seal.unlink()
        seal.with_name('kernel-result.json').unlink()
        with self.assertRaisesRegex(ValueError, 'without replay'):
            C.reject_missing_successful_objects(self.f.stage, [TARGET])

    def test_deployment_rejects_original_stage_or_provider_before_writes(self):
        package = self.f.base / 'empty-package'
        package.mkdir()
        for forbidden in (self.f.origin, self.f.fields, self.f.provider / 'evidence'):
            before = sorted(str(p.relative_to(forbidden)) for p in forbidden.rglob('*'))
            with self.assertRaisesRegex(ValueError, 'disjoint'):
                S.install_package(package, forbidden)
            self.assertEqual(before, sorted(str(p.relative_to(forbidden)) for p in forbidden.rglob('*')))

    def test_export_selects_one_new_object_and_no_old_88_objects(self):
        self.f.success()
        config = {'targets': [self.f.target], 'workflow_files': []}
        put(self.f.here / 'SHAPE_REPAIR_VERIFIER.json', config)
        entries = select_new_evidence(self.f.stage, self.f.here, config)
        self.assertEqual([name for name in entries if name.endswith('.olean')],
                         ['objects/' + TARGET.replace('.', '/') + '.olean'])
        wrong = copy.deepcopy(config)
        wrong['targets'][0]['module'] = 'ImbalancedChen.Other'
        with self.assertRaisesRegex(ValueError, 'fixed ShapeArrays'):
            select_new_evidence(self.f.stage, self.f.here, wrong)


if __name__ == '__main__':
    unittest.main()
