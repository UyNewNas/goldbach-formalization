#!/usr/bin/env python3
"""Synthetic local workflow regressions. These fixtures are not Lean evidence."""
from pathlib import Path
import copy
import json
import os
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
from receipt_checks import (MODES, TOOL_REL, canonical, expected_argv, fp, prior, read,
                            reject_missing_successful_objects, target_paths, validate_layout,
                            validate_step, validate_success)
from export_connections14 import data_pin, recheck_archive, write_verified_archive


def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value if isinstance(value, str) else json.dumps(value, indent=2) + '\n')


class Fixture:
    def __init__(self, count=1):
        self.temp = tempfile.TemporaryDirectory(prefix='p26-cell05-workflow-', dir=Path(__file__).absolute().parent)
        self.base = Path(self.temp.name)
        self.stage = self.base / 'stage'
        self.here = self.stage / TOOL_REL
        self.here.mkdir(parents=True)
        self.provider_source, self.provider_object = self.base / 'provider-source', self.base / 'provider-object'
        self.provider_source.mkdir()
        self.provider_object.mkdir()
        self.modules = [f'ImbalancedChen.SyntheticCell05Workflow{i:02d}' for i in range(count)]
        targets = []
        for module in self.modules:
            relative = Path(module.replace('.', '/'))
            source = self.stage / 'project' / relative.with_suffix('.lean')
            origin = self.stage / 'sources' / relative.with_suffix('.lean')
            obj = self.stage / 'objects' / relative.with_suffix('.olean')
            audit = self.here / 'owned-audits' / (relative.name + '.lean')
            put(source, '-- SYNTHETIC TEST, NEVER LEAN PROOF\n')
            put(origin, source.read_text())
            put(obj, 'SYNTHETIC OBJECT BYTES\n')
            put(audit, '-- SYNTHETIC AUDIT\n')
            targets.append({'module': module, 'source': fp(source), 'audit': fp(audit),
                            'project_imports': [], 'transitive_dependencies': []})
        lean = self.base / 'toolchain/bin/lean'
        checker = lean.with_name('leanchecker')
        put(lean, 'SYNTHETIC NONEXECUTABLE BINARY\n')
        put(checker, 'SYNTHETIC NONEXECUTABLE CHECKER\n')
        mathlib = self.base / 'mathlib-objects'
        mathlib.mkdir()
        frozen = [fp(target_paths({'stage': str(self.stage)}, module)[kind])
                  for module in self.modules for kind in ('source', 'audit')]
        self.context = {'schema': 'cell05_connections14_context_v1', 'stage': str(self.stage),
                        'cwd': str(self.stage / 'project'), 'objects': str(self.stage / 'objects'),
                        'targets': targets, 'suppliers': [], 'frozen_inputs': frozen,
                        'runtime': {'lean_binary': fp(lean), 'leanchecker_binary': fp(checker)},
                        'mathlib_package_object_roots': [], 'mathlib_objects': str(mathlib),
                        'environment': {'LEAN_PATH': os.pathsep.join([str(self.stage / 'objects'), str(mathlib)]),
                                        'LEAN_SYSROOT': str(lean.parent.parent), 'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1'},
                        'rss_limit_bytes': 6 * 1024**3, 'wall_limit_seconds': 900,
                        'old_supplier_proof_commands': 0, 'cloud_source_generation': False}
        from runtime_compat import stat_identity
        self.guard_path = self.base / 'provider/RUNTIME_GUARD.json'
        put(self.guard_path, {'schema': 'cell05_connections_runtime_guard_v1',
                             'all_selected_bytes_rehashed_before_guard': True,
                             'entries': [{'path': str(lean), 'lstat': stat_identity(lean)}]})
        self.context['runtime_guard'] = fp(self.guard_path)
        join_path = self.here / 'SUPPLIER_JOIN.json'
        put(join_path, {'runtime_guard': self.context['runtime_guard']})
        self.context['supplier_join'] = fp(join_path)
        self.context['frozen_inputs'] += [fp(self.guard_path), fp(join_path)]
        self.run_root = self.stage / 'verification/attempt_1'
        self.run = self.run_root / 'RUN.json'
        put(self.run, {'schema': 'cell05_connections14_run_v1', 'attempt': 'attempt_1', 'context': self.context})

    def close(self):
        self.temp.cleanup()

    def step(self, module, mode):
        paths = target_paths(self.context, module)
        folder = self.run_root / module.split('.')[-1]
        command_path, result_path, seal_path = [folder / (mode + suffix) for suffix in ('-command.json', '-result.json', '-accepted.json')]
        command = {'schema': 'cell05_connections14_step_command_v1', 'run': fp(self.run), 'module': module, 'mode': mode,
                   'argv': expected_argv(self.context, module, mode), 'cwd': self.context['cwd'],
                   'environment': self.context['environment'], 'source': fp(paths['source']),
                   'audit_source': fp(paths['audit']) if mode == 'owned' else None,
                   'dependency_objects': {}, 'object_before': None if mode == 'normal' else fp(paths['object'])}
        put(command_path, command)
        log_path = folder / (mode + '.log')
        if mode == 'kernel':
            log = 'replaying ' + module + '\n'
        elif mode == 'normal':
            log = 'SYNTHETIC NORMAL TEST LOG\n'
        else:
            name = module + '.syntheticDecl'
            inventory = {'module': module, 'environment': [name], 'serialized': [name]}
            declaration = {'module': module, 'name': name, 'type': 'True', 'unsafe': False,
                           'partial': False, 'axiom': False, 'axioms': []}
            complete = {'module': module, 'count': 1}
            log = ''.join(marker + json.dumps(item) + '\n' for marker, item in [
                ('P26_GEOMETRY01_AUDIT_IMPORTS ', [module]), ('P26_GEOMETRY01_AUDIT_INVENTORY ', inventory), ('P26_GEOMETRY01_AUDIT_DECL ', declaration),
                ('P26_GEOMETRY01_AUDIT_COMPLETE ', complete)])
        put(log_path, log)
        result = {'schema': 'cell05_connections14_step_result_v1', 'run': fp(self.run), 'command': fp(command_path),
                  'module': module, 'mode': mode, 'status': 'succeeded', 'exit_code': 0, 'termination_reason': None,
                  'source': command['source'], 'audit_source': command['audit_source'], 'dependency_objects': {},
                  'object': fp(paths['object']), 'log': fp(log_path), 'elapsed_seconds': 0.01, 'peak_rss_bytes': 1}
        if mode == 'normal':
            result['printed_axioms'] = []
        elif mode == 'owned':
            from receipt_support import parse_owned
            owned_path = folder / 'owned-declarations.json'
            put(owned_path, parse_owned(log, module))
            result['owned_declarations'], result['owned_declaration_count'] = fp(owned_path), 1
        put(result_path, result)
        put(seal_path, {'schema': 'cell05_connections14_step_accepted_v1', 'status': 'accepted', 'module': module, 'mode': mode,
                        'run': fp(self.run), 'command': fp(command_path), 'result': fp(result_path), 'object': result['object']})
        return seal_path

    def reseal(self, path, command_change=None, result_change=None, seal_change=None):
        seal = read(path)
        cmd_path, result_path = Path(seal['command']['path']), Path(seal['result']['path'])
        command, result = read(cmd_path), read(result_path)
        command['run'] = fp(self.run)
        if command_change:
            command_change(command)
        put(cmd_path, command)
        result['run'], result['command'] = fp(self.run), fp(cmd_path)
        if result_change:
            result_change(result)
        put(result_path, result)
        seal.update(run=fp(self.run), command=fp(cmd_path), result=fp(result_path))
        if seal_change:
            seal_change(seal)
        put(path, seal)


class ChangedWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.f = Fixture(14)
        self.module = self.f.modules[0]

    def tearDown(self):
        self.f.close()

    def reusable(self):
        return {(module, mode): prior(self.f.context, module, mode)
                for module in self.f.modules for mode in MODES}

    def test_pilot_three_steps_are_an_immutable_reusable_prefix(self):
        from receipt_checks import require_accepted_prefix
        records = []
        for mode in MODES:
            seal = self.f.step(self.module, mode)
            validate_step(fp(seal), self.f.context, self.module, mode)
            records.append({'module': self.module, 'mode': mode, 'accepted': fp(seal), 'disposition': 'executed'})
        put(self.f.run_root / 'STOPPED.json', {'status': 'stopped', 'reason': 'new_step_budget',
            'run': fp(self.f.run), 'records': records})
        self.assertEqual(require_accepted_prefix(self.f.context, self.reusable()), 3)
        self.assertFalse((self.f.run_root / 'SUCCESS.json').exists())
        reject_missing_successful_objects(self.f.stage, self.f.modules)

    def test_success_requires_all_fourteen_triples(self):
        records = []
        for module in self.f.modules:
            for mode in MODES:
                seal = self.f.step(module, mode)
                records.append({'module': module, 'mode': mode, 'accepted': fp(seal), 'disposition': 'executed'})
        success = {'schema': 'cell05_connections14_success_v1', 'status': 'succeeded', 'run': fp(self.f.run),
                   'context': self.f.context, 'records': records, 'accepted_targets': 14, 'accepted_steps': 42,
                   'newly_executed_steps': 42, 'reused_steps': 0, 'frozen_inputs_unchanged': True,
                   'whole_geometry_decoded': False, 'P2_6_complete': False}
        path = self.f.run_root / 'SUCCESS.json'
        put(path, success)
        self.assertEqual(len(validate_success(path)[1]), 42)
        success['records'] = records[:3]
        success.update(accepted_targets=1, accepted_steps=3, newly_executed_steps=3)
        put(path, success)
        with self.assertRaisesRegex(ValueError, '42-step'):
            validate_success(path)

    def test_missing_success_object_or_seal_is_never_a_cache_miss(self):
        seal = self.f.step(self.module, 'normal')
        obj = target_paths(self.f.context, self.module)['object']
        body = obj.read_bytes()
        obj.unlink()
        with self.assertRaises(ValueError):
            reject_missing_successful_objects(self.f.stage, self.f.modules)
        obj.write_bytes(body)
        seal.unlink()
        with self.assertRaisesRegex(ValueError, 'lacks its acceptance seal'):
            prior(self.f.context, self.module, 'normal')

    def test_index_keeps_barrier_if_result_and_seal_disappear(self):
        seal = self.f.step(self.module, 'normal')
        put(self.f.run_root / 'STOPPED.json', {'status': 'stopped', 'run': fp(self.f.run), 'records': [
            {'module': self.module, 'mode': 'normal', 'accepted': fp(seal), 'disposition': 'executed'}]})
        seal.unlink()
        seal.with_name('normal-result.json').unlink()
        with self.assertRaises(ValueError):
            reject_missing_successful_objects(self.f.stage, self.f.modules)

    def test_orphan_command_and_log_stop_ambiguous_replay(self):
        seal = self.f.step(self.module, 'kernel')
        seal.unlink()
        seal.with_name('kernel-result.json').unlink()
        with self.assertRaisesRegex(ValueError, 'without replay'):
            reject_missing_successful_objects(self.f.stage, self.f.modules)

    def test_runtime_stat_change_blocks_existing_receipts(self):
        seal = self.f.step(self.module, 'normal')
        lean = Path(self.f.context['runtime']['lean_binary']['path'])
        # Same bytes and size still alter the original inode metadata.
        lean.write_bytes(lean.read_bytes())
        with self.assertRaisesRegex(RuntimeError, 'runtime file/directory changed'):
            validate_step(fp(seal), self.f.context, self.module, 'normal')

    def test_guard_recapture_cannot_resume_old_receipts(self):
        seal = self.f.step(self.module, 'normal')
        altered = copy.deepcopy(self.f.context)
        altered['runtime_guard'] = dict(altered['runtime_guard'], sha256='0' * 64)
        with self.assertRaisesRegex(ValueError, 'Prior RUN differs'):
            validate_step(fp(seal), altered, self.module, 'normal', check_inputs=False)

    def test_gap_cannot_replay_missing_normal_before_accepted_kernel(self):
        from receipt_checks import require_accepted_prefix
        self.f.step(self.module, 'kernel')
        with self.assertRaisesRegex(ValueError, 'gap'):
            require_accepted_prefix(self.f.context, self.reusable())

    def test_wrong_owned_project_import_is_rejected(self):
        seal = self.f.step(self.module, 'owned')
        log = seal.with_name('owned.log')
        body = log.read_text().replace(json.dumps([self.module]), json.dumps([self.module, 'ImbalancedChen.Unaccepted']))
        log.write_text(body)
        self.f.reseal(seal, result_change=lambda value: value.update(log=fp(log)))
        with self.assertRaisesRegex(ValueError, 'project import closure'):
            validate_step(fp(seal), self.f.context, self.module, 'owned')

    def test_existing_different_object_is_not_overwritten(self):
        from verify_connections14 import install
        source, destination = self.f.base / 'old.olean', self.f.base / 'new.olean'
        put(source, 'OLD ACCEPTED BYTES')
        put(destination, 'DIFFERENT BYTES')
        with self.assertRaisesRegex(ValueError, 'Refusing overwrite'):
            install(source, destination, fp(source))
        self.assertEqual(destination.read_text(), 'DIFFERENT BYTES')

    def test_archive_regular_bytes_readback_and_tamper_detection(self):
        source = self.f.base / 'source.txt'
        put(source, 'SYNTHETIC EVIDENCE')
        manifest = {'members': [{'member': 'new/source.txt', **data_pin(source.read_bytes())}]}
        output = self.f.base / 'export.tar.xz'
        write_verified_archive(output, {'new/source.txt': source}, manifest)
        recheck_archive(output, manifest)
        altered = copy.deepcopy(manifest)
        altered['members'][0]['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            recheck_archive(output, altered)


if __name__ == '__main__':
    unittest.main()
