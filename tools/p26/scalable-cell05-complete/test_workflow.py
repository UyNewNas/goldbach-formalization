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
from export_phase1 import data_pin, recheck_archive, write_verified_archive


def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value if isinstance(value, str) else json.dumps(value, indent=2) + '\n')


class Fixture:
    def __init__(self, count=1):
        self.temp = tempfile.TemporaryDirectory(prefix='p26-cell05-workflow-', dir='/dev/shm')
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
        self.context = {'schema': 'cell05_complete_context_v2', 'stage': str(self.stage),
                        'cwd': str(self.stage / 'project'), 'objects': str(self.stage / 'objects'),
                        'targets': targets, 'suppliers': [], 'frozen_inputs': frozen,
                        'runtime': {'lean_binary': fp(lean), 'leanchecker_binary': fp(checker)},
                        'mathlib_package_object_roots': [], 'mathlib_objects': str(mathlib),
                        'environment': {'LEAN_PATH': os.pathsep.join([str(self.stage / 'objects'), str(mathlib)]),
                                        'LEAN_SYSROOT': str(lean.parent.parent), 'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1'},
                        'rss_limit_bytes': 6 * 1024**3, 'wall_limit_seconds': 900,
                        'old_supplier_proof_commands': 0, 'cloud_source_generation': False}
        self.run_root = self.stage / 'verification/attempt_1'
        self.run = self.run_root / 'RUN.json'
        put(self.run, {'schema': 'cell05_complete_run_v2', 'attempt': 'attempt_1', 'context': self.context})

    def close(self):
        self.temp.cleanup()

    def step(self, module, mode):
        paths = target_paths(self.context, module)
        folder = self.run_root / module.split('.')[-1]
        command_path, result_path, seal_path = [folder / (mode + suffix) for suffix in ('-command.json', '-result.json', '-accepted.json')]
        command = {'schema': 'cell05_step_command_v2', 'run': fp(self.run), 'module': module, 'mode': mode,
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
                ('P26_GEOMETRY01_AUDIT_INVENTORY ', inventory), ('P26_GEOMETRY01_AUDIT_DECL ', declaration),
                ('P26_GEOMETRY01_AUDIT_COMPLETE ', complete)])
        put(log_path, log)
        result = {'schema': 'cell05_step_result_v2', 'run': fp(self.run), 'command': fp(command_path),
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
        put(seal_path, {'schema': 'cell05_step_accepted_v2', 'status': 'accepted', 'module': module, 'mode': mode,
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


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()
        self.module = self.f.modules[0]

    def tearDown(self):
        self.f.close()

    def check(self, path, mode):
        return validate_step(fp(path), self.f.context, self.module, mode)

    def test_valid_three_step_chain_and_partial_resume(self):
        for mode in MODES:
            path = self.f.step(self.module, mode)
            self.check(path, mode)
            self.assertEqual(prior(self.f.context, self.module, mode)['accepted'], fp(path))
        self.assertFalse((self.f.run_root / 'SUCCESS.json').exists())

    def test_missing_successful_normal_object_refuses_rebuild(self):
        self.f.step(self.module, 'normal')
        target_paths(self.f.context, self.module)['object'].unlink()
        with self.assertRaisesRegex(ValueError, 'missing'):
            reject_missing_successful_objects(self.f.stage, self.f.modules)
        with self.assertRaisesRegex(ValueError, 'missing'):
            prior(self.f.context, self.module, 'normal')

    def test_success_without_seal_is_not_replayed(self):
        self.f.step(self.module, 'normal').unlink()
        with self.assertRaisesRegex(ValueError, 'lacks its acceptance seal'):
            prior(self.f.context, self.module, 'normal')

    def test_seal_without_result_and_object_stops_resume(self):
        seal_path = self.f.step(self.module, 'normal')
        self.check(seal_path, 'normal')
        Path(read(seal_path)['result']['path']).unlink()
        target_paths(self.f.context, self.module)['object'].unlink()
        for name, action in [
                ('before_writes', lambda: reject_missing_successful_objects(self.f.stage, self.f.modules)),
                ('prior_lookup', lambda: prior(self.f.context, self.module, 'normal'))]:
            with self.subTest(gate=name):
                with self.assertRaises(ValueError):
                    action()
        self.assertTrue(seal_path.exists())
        self.assertFalse(target_paths(self.f.context, self.module)['object'].exists())
        # A surviving STOPPED index is also an acceptance marker when the
        # per-step seal itself has been lost; it must not permit replay.
        put(self.f.run_root / 'STOPPED.json', {'status': 'stopped', 'run': fp(self.f.run),
            'records': [{'module': self.module, 'mode': 'normal', 'accepted': fp(seal_path), 'disposition': 'executed'}]})
        seal_path.unlink()
        for name, action in [
                ('indexed_before_writes', lambda: reject_missing_successful_objects(self.f.stage, self.f.modules)),
                ('indexed_prior_lookup', lambda: prior(self.f.context, self.module, 'normal'))]:
            with self.subTest(gate=name):
                with self.assertRaises(ValueError):
                    action()

    def test_wrong_explicit_module_even_after_resealing(self):
        path = self.f.step(self.module, 'normal')
        self.f.reseal(path, command_change=lambda row: row.update(module='ImbalancedChen.Wrong'))
        with self.assertRaisesRegex(ValueError, 'module/mode'):
            self.check(path, 'normal')

    def test_wrong_explicit_mode_even_after_resealing(self):
        path = self.f.step(self.module, 'kernel')
        self.f.reseal(path, result_change=lambda row: row.update(mode='normal'))
        with self.assertRaisesRegex(ValueError, 'module/mode'):
            self.check(path, 'kernel')

    def test_wrong_checker_target_even_after_resealing(self):
        path = self.f.step(self.module, 'kernel')
        self.f.reseal(path, command_change=lambda row: row['argv'].__setitem__(-1, 'ImbalancedChen.Wrong'))
        with self.assertRaisesRegex(ValueError, 'argv'):
            self.check(path, 'kernel')

    def test_wrong_normal_output_argv_even_after_resealing(self):
        path = self.f.step(self.module, 'normal')
        self.f.reseal(path, command_change=lambda row: row['argv'].__setitem__(-2, '/elsewhere/target.olean'))
        with self.assertRaisesRegex(ValueError, 'argv'):
            self.check(path, 'normal')

    def test_normal_object_before_must_be_absent(self):
        path = self.f.step(self.module, 'normal')
        obj = fp(target_paths(self.f.context, self.module)['object'])
        self.f.reseal(path, command_change=lambda row: row.update(object_before=obj))
        with self.assertRaisesRegex(ValueError, 'object_before'):
            self.check(path, 'normal')

    def test_kernel_object_before_must_be_exact(self):
        path = self.f.step(self.module, 'kernel')
        self.f.reseal(path, command_change=lambda row: row.update(object_before=None))
        with self.assertRaisesRegex(ValueError, 'object_before'):
            self.check(path, 'kernel')

    def test_same_bytes_source_outside_stage_rejected(self):
        path = self.f.step(self.module, 'normal')
        outside = self.f.base / 'same-source.lean'
        put(outside, target_paths(self.f.context, self.module)['source'].read_text())
        self.f.reseal(path, command_change=lambda row: row.update(source=fp(outside)),
                      result_change=lambda row: row.update(source=fp(outside)))
        with self.assertRaisesRegex(ValueError, 'current exact stage files'):
            self.check(path, 'normal')

    def test_same_bytes_object_outside_stage_rejected(self):
        path = self.f.step(self.module, 'kernel')
        outside = self.f.base / 'same-object.olean'
        put(outside, target_paths(self.f.context, self.module)['object'].read_text())
        self.f.reseal(path, result_change=lambda row: row.update(object=fp(outside)),
                      seal_change=lambda row: row.update(object=fp(outside)))
        with self.assertRaisesRegex(ValueError, 'current exact stage object'):
            self.check(path, 'kernel')

    def test_same_bytes_audit_outside_stage_rejected(self):
        path = self.f.step(self.module, 'owned')
        outside = self.f.base / 'same-audit.lean'
        put(outside, target_paths(self.f.context, self.module)['audit'].read_text())
        self.f.reseal(path, command_change=lambda row: row.update(audit_source=fp(outside)),
                      result_change=lambda row: row.update(audit_source=fp(outside)))
        with self.assertRaisesRegex(ValueError, 'current exact stage files'):
            self.check(path, 'owned')

    def test_changed_package_root_blocks_prior_reuse(self):
        self.f.step(self.module, 'normal')
        altered = copy.deepcopy(self.f.context)
        altered['mathlib_package_object_roots'] = [str(self.f.base / 'other-packages')]
        with self.assertRaisesRegex(ValueError, 'Prior RUN differs'):
            prior(altered, self.module, 'normal')

    def test_changed_cwd_blocks_prior_reuse(self):
        self.f.step(self.module, 'normal')
        altered = copy.deepcopy(self.f.context)
        altered['cwd'] = str(self.f.base / 'other-project')
        with self.assertRaisesRegex(ValueError, 'Prior RUN differs'):
            prior(altered, self.module, 'normal')

    def test_changed_lean_path_blocks_prior_reuse(self):
        self.f.step(self.module, 'normal')
        altered = copy.deepcopy(self.f.context)
        altered['environment']['LEAN_PATH'] += ':/other'
        with self.assertRaisesRegex(ValueError, 'Prior RUN differs'):
            prior(altered, self.module, 'normal')

    def test_command_environment_must_match_run(self):
        path = self.f.step(self.module, 'normal')
        self.f.reseal(path, command_change=lambda row: row['environment'].update(LEAN_NUM_THREADS='8'))
        with self.assertRaisesRegex(ValueError, 'cwd/environment'):
            self.check(path, 'normal')

    def test_changed_log_without_new_receipt_rejected(self):
        path = self.f.step(self.module, 'kernel')
        put(path.with_name('kernel.log'), 'replaying ImbalancedChen.Wrong\n')
        with self.assertRaisesRegex(ValueError, 'Log path or fingerprint'):
            self.check(path, 'kernel')

    def test_changed_run_without_new_receipt_rejected(self):
        path = self.f.step(self.module, 'normal')
        value = read(self.f.run)
        value['attempt'] = 'different_attempt'
        put(self.f.run, value)
        with self.assertRaisesRegex(ValueError, 'Fingerprint changed'):
            self.check(path, 'normal')

    def test_changed_command_without_new_receipt_rejected(self):
        path = self.f.step(self.module, 'normal')
        command = path.with_name('normal-command.json')
        value = read(command)
        value['argv'].append('--unexpected')
        put(command, value)
        with self.assertRaisesRegex(ValueError, 'Fingerprint changed'):
            self.check(path, 'normal')

    def test_changed_successful_object_is_not_recompiled(self):
        self.f.step(self.module, 'normal')
        put(target_paths(self.f.context, self.module)['object'], 'DIFFERENT OBJECT BYTES\n')
        with self.assertRaisesRegex(ValueError, 'current exact stage object'):
            prior(self.f.context, self.module, 'normal')

    def test_owned_inventory_missing_decl_rejected(self):
        path = self.f.step(self.module, 'owned')
        log_path = path.with_name('owned.log')
        put(log_path, '\n'.join(line for line in log_path.read_text().splitlines() if not line.startswith('P26_GEOMETRY01_AUDIT_DECL ')) + '\n')
        self.f.reseal(path, result_change=lambda row: row.update(log=fp(log_path)))
        with self.assertRaises(AssertionError):
            self.check(path, 'owned')

    def layout(self, **overrides):
        values = dict(stage=self.f.stage, here=self.f.here, supplier_project=self.f.provider_source,
                      supplier_objects=self.f.provider_object, modules=self.f.modules, targets=self.f.modules,
                      attempt='attempt_2')
        values.update(overrides)
        return validate_layout(**values)

    def test_object_ancestor_symlink_rejected_before_any_write(self):
        namespace = self.f.stage / 'objects/ImbalancedChen'
        outside = self.f.base / 'outside-objects'
        namespace.rename(outside)
        namespace.symlink_to(outside, target_is_directory=True)
        before = sorted(p.name for p in outside.iterdir())
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            self.layout()
        self.assertEqual(sorted(p.name for p in outside.iterdir()), before)
        self.assertFalse((self.f.stage / 'verification/attempt_2').exists())

    def test_verification_ancestor_symlink_rejected_before_any_write(self):
        verification = self.f.stage / 'verification'
        outside = self.f.base / 'outside-verification'
        verification.rename(outside)
        verification.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            self.layout()
        self.assertFalse((outside / 'attempt_2').exists())

    def test_provider_ancestor_symlink_rejected_before_any_write(self):
        link = self.f.base / 'provider-link'
        link.symlink_to(self.f.provider_source, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            self.layout(supplier_project=link)
        self.assertFalse((self.f.stage / 'verification/attempt_2').exists())

    def test_dangling_final_object_symlink_rejected_before_any_write(self):
        obj = target_paths(self.f.context, self.module)['object']
        obj.unlink()
        obj.symlink_to(self.f.base / 'nonexistent-object')
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            self.layout()
        self.assertFalse((self.f.base / 'nonexistent-object').exists())
        self.assertFalse((self.f.stage / 'verification/attempt_2').exists())

    def test_provider_contains_stage_rejected(self):
        with self.assertRaisesRegex(ValueError, 'disjoint in both directions'):
            self.layout(supplier_project=self.f.base)

    def test_stage_contains_provider_rejected(self):
        provider = self.f.stage / 'provider'
        provider.mkdir()
        with self.assertRaisesRegex(ValueError, 'disjoint in both directions'):
            self.layout(supplier_project=provider)

    def test_unknown_object_module_rejected(self):
        put(self.f.stage / 'objects/ImbalancedChen/Unknown.olean', 'unknown\n')
        with self.assertRaisesRegex(ValueError, 'Unknown module or sidecar'):
            self.layout()

    def test_unknown_object_sidecar_rejected(self):
        obj = target_paths(self.f.context, self.module)['object']
        put(obj.with_name(obj.name + '.server'), 'unexpected\n')
        with self.assertRaisesRegex(ValueError, 'Unknown module or sidecar'):
            self.layout()

    def test_success_45_chains_resume_counts_and_export_gate(self):
        f = Fixture(15)
        try:
            records = []
            for module in f.modules:
                for mode in MODES:
                    path = f.step(module, mode)
                    records.append({'module': module, 'mode': mode, 'accepted': fp(path), 'disposition': 'reused'})
            run = f.stage / 'verification/attempt_2/RUN.json'
            put(run, {'schema': 'cell05_complete_run_v2', 'attempt': 'attempt_2', 'context': f.context})
            success = run.with_name('SUCCESS.json')
            value = {'schema': 'cell05_complete_success_v2', 'status': 'succeeded', 'run': fp(run), 'context': f.context,
                     'records': records, 'accepted_targets': 15, 'accepted_steps': 45, 'newly_executed_steps': 0,
                     'reused_steps': 45, 'frozen_inputs_unchanged': True, 'whole_geometry_decoded': False, 'P2_6_complete': False}
            put(success, value)
            _, steps = validate_success(success)
            self.assertEqual(len(steps), 45)
            value['newly_executed_steps'] = 45
            put(success, value)
            with self.assertRaisesRegex(ValueError, 'execution counts'):
                validate_success(success)
        finally:
            f.close()

    def test_archive_roundtrip_and_member_recheck(self):
        source = self.f.base / 'selected.txt'
        put(source, 'original selected bytes\n')
        manifest = {'status': 'SYNTHETIC_NOT_LEAN_EVIDENCE', 'members': [{'member': 'selected.txt', **data_pin(source.read_bytes())}]}
        output = self.f.stage / 'exports/fixture.tar.xz'
        identity = write_verified_archive(output, {'selected.txt': source}, manifest)
        self.assertEqual(identity, fp(output))
        recheck_archive(output, manifest)

    def test_hardlinked_source_project_archive_roundtrip(self):
        relative = Path(self.module.replace('.', '/')).with_suffix('.lean')
        origin = self.f.stage / 'sources' / relative
        installed = self.f.stage / 'project' / relative
        installed.unlink()
        os.link(origin, installed)
        self.assertEqual(origin.stat().st_ino, installed.stat().st_ino)
        entries = {'sources/original.lean': origin, 'project/original.lean': installed}
        manifest = {'status': 'SYNTHETIC_NOT_LEAN_EVIDENCE', 'members': [
            {'member': member, **data_pin(path.read_bytes())} for member, path in entries.items()]}
        output = self.f.stage / 'exports/hardlinked.tar.xz'
        write_verified_archive(output, entries, manifest)
        recheck_archive(output, manifest)
        with tarfile.open(output) as archive:
            self.assertTrue(all(item.isfile() for item in archive.getmembers()))
            self.assertEqual(archive.extractfile('sources/original.lean').read(), origin.read_bytes())
            self.assertEqual(archive.extractfile('project/original.lean').read(), installed.read_bytes())

    def test_archive_input_change_during_pack_is_rejected(self):
        source = self.f.base / 'selected.txt'
        put(source, 'original selected bytes\n')
        manifest = {'status': 'SYNTHETIC_NOT_LEAN_EVIDENCE', 'members': [{'member': 'selected.txt', **data_pin(source.read_bytes())}]}
        output = self.f.stage / 'exports/changed.tar.xz'
        original_addfile = tarfile.TarFile.addfile

        def mutate_after_read(archive, info, *args, **kwargs):
            result = original_addfile(archive, info, *args, **kwargs)
            if info.name == 'selected.txt':
                put(source, 'changed during packing\n')
            return result

        with mock.patch.object(tarfile.TarFile, 'addfile', mutate_after_read):
            with self.assertRaisesRegex(ValueError, 'Input changed while packing'):
                write_verified_archive(output, {'selected.txt': source}, manifest)
        self.assertFalse(output.exists())
        self.assertTrue(output.with_name(output.name + '.partial').exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
