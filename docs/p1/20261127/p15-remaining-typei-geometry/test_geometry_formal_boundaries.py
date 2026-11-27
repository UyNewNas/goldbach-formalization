"""New Geometry entry boundaries only; no Lean, cloud, or old acceptance reruns."""
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
import copy
import contextlib
import io
import json
import tempfile
import unittest

import run_geometry as geometry
import install_geometry_source as installer


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


def artifact_fixture(module):
    return [module + '/artifact-' + str(index) for index in range(21)]


def dependency_fixture():
    modules = {'ImbalancedChen.Fixture' + str(index) for index in range(142)}
    active = modules | {geometry.RESERVE, geometry.ROUGH}
    dependencies = (modules - {'ImbalancedChen.Fixture0', 'ImbalancedChen.Fixture1'}) | {geometry.RESERVE}
    old = {m: dict.fromkeys(artifact_fixture(m)) for m in modules}
    reserve = dict.fromkeys(artifact_fixture(geometry.RESERVE))
    reserve[geometry.RESERVE + '/artifact-0'] = {'bytes': 17, 'sha256': '1' * 64}
    bindings = {
        geometry.RESERVE: {'all_observed_target_artifacts': reserve},
        geometry.ROUGH: {'all_observed_target_artifacts': dict.fromkeys(artifact_fixture(geometry.ROUGH))}}
    return SimpleNamespace(active=active, baseline={'preserved_dependency_artifacts': old}), bindings, dependencies


class GeometryFormalBoundaries(unittest.TestCase):
    def test_unbound_actual_probe_cannot_enter_publication_or_runtime_reads(self):
        with self.assertRaisesRegex(RuntimeError, 'unbound'):
            geometry.validate_inputs(geometry.INPUTS)

    def test_any_previous_attempt_prevents_automatic_retry(self):
        with tempfile.TemporaryDirectory() as temporary:
            runs = Path(temporary) / 'runs'
            geometry.require_new_attempt(runs)
            attempt = runs / 'attempt-00000'
            attempt.mkdir(parents=True)
            for filename in (None, 'RESULT.json'):
                if filename:
                    (attempt / filename).write_text('{"new_owner_accepted": true}')
                with self.subTest(filename=filename):
                    with self.assertRaisesRegex(RuntimeError, 'history'):
                        geometry.require_new_attempt(runs)
                    self.assertTrue(attempt.is_dir())

    def test_dependency_subset_keeps_reserve_owner_full_21_pins_and_excludes_rough(self):
        ag, bindings, dependencies = dependency_fixture()
        pins = geometry.dependency_inventory(ag, bindings, dependencies, artifact_fixture)
        self.assertEqual(len(pins), 141)
        self.assertTrue(all(len(row) == 21 for row in pins.values()))
        self.assertNotIn(geometry.ROUGH, pins)
        self.assertEqual(pins[geometry.RESERVE][geometry.RESERVE + '/artifact-0'],
                         {'bytes': 17, 'sha256': '1' * 64})
        self.assertEqual(len(ag.baseline['preserved_dependency_artifacts']), 142)

    def test_fixed_two_artifact_pins_cannot_replace_original_full_inventory(self):
        ag, bindings, dependencies = dependency_fixture()
        victim = 'ImbalancedChen.Fixture2'
        ag.baseline['preserved_dependency_artifacts'][victim] = {
            victim + '/artifact-0': None, victim + '/artifact-1': None}
        with self.assertRaisesRegex(RuntimeError, '21-artifact'):
            geometry.dependency_inventory(ag, bindings, dependencies, artifact_fixture)
        ag, bindings, dependencies = dependency_fixture()
        del bindings[geometry.RESERVE]
        with self.assertRaisesRegex(RuntimeError, 'owner dependency binding'):
            geometry.dependency_inventory(ag, bindings, dependencies, artifact_fixture)

    def test_source_install_success_cannot_cross_commit_or_hide_failure(self):
        identity = {'source_commit': 'a' * 40}
        worker = {'schema': 'p15_independent_geometry_source_install_v1', 'identity': identity,
            'new_owner_accepted': False, 'whole_P1_5_complete': False,
            'normal_or_kernel_commands_executed': 0, 'source_installed': True,
            'source_before': None, 'source_after': geometry.SOURCE_FP,
            'installation_action': 'EXCLUSIVE_NEW_CANONICAL_SOURCE'}
        result = {**worker, 'worker_exit_code': 0, 'source_install_complete': True}
        geometry.require_terminal(result, worker, identity, installation=True)
        with self.assertRaisesRegex(RuntimeError, 'identity'):
            geometry.require_terminal(result, worker, {'source_commit': 'b' * 40}, installation=True)
        bad_worker = {**worker, 'preservation_error': 'AI evidence changed'}
        bad_result = {**bad_worker, 'worker_exit_code': 0, 'source_install_complete': True}
        with self.assertRaisesRegex(RuntimeError, 'failure binding'):
            geometry.require_terminal(bad_result, bad_worker, identity, installation=True)
        bad_result = {**result, 'new_owner_accepted': True}
        with self.assertRaisesRegex(RuntimeError, 'terminal success'):
            geometry.require_terminal(bad_result, worker, identity, installation=True)

    def test_partial_geometry_artifacts_or_history_block_source_installation(self):
        empty = {str(i): None for i in range(21)}
        geometry.require_new_slot(geometry.ORIGINAL_SOURCE_FP, empty, [], installed=False)
        for artifacts, history in (({**empty, '0': {'bytes': 1, 'sha256': '2' * 64}}, []),
                                   (empty, ['/old/started-owner'])):
            with self.subTest(history=history):
                with self.assertRaisesRegex(RuntimeError, 'history or artifacts'):
                    geometry.require_new_slot(geometry.ORIGINAL_SOURCE_FP, artifacts, history, installed=False)
        with self.assertRaisesRegex(RuntimeError, 'canonical source differs'):
            geometry.require_new_slot(geometry.ORIGINAL_SOURCE_FP, empty, [], installed=True)

    def test_preparation_failure_is_saved_by_both_workers_without_acceptance(self):
        def denied_lane(_):
            raise RuntimeError('test lane refused before preparation')
        for install in (False, True):
            with tempfile.TemporaryDirectory() as temporary, self.subTest(installation=install):
                run = Path(temporary)
                c = SimpleNamespace(identity={'source_commit': 'a' * 40}, installer=b'exact installer',
                    ag=SimpleNamespace(d=SimpleNamespace(verify_lane=denied_lane, save=save), h=object()))
                code = installer.worker(geometry, c, run) if install else geometry.worker(c, run)
                row = json.loads((run / 'WORKER_RESULT.json').read_text())
                self.assertEqual(code, 1)
                self.assertIs(row['new_owner_accepted'], False)
                self.assertIs(row['whole_P1_5_complete'], False)
                self.assertIn('test lane refused', row['installation_error'] if install
                              else row['failures'][geometry.TARGET])

    def test_dispatch_preparation_failure_preserves_result_and_git_after(self):
        def attempt(runs):
            result = runs / 'attempt-00000'; result.mkdir(parents=True); return result
        def denied_frozen_write(path, raw):
            raise OSError('test frozen write refused')
        for install in (False, True):
            with tempfile.TemporaryDirectory() as temporary, self.subTest(installation=install):
                root = Path(temporary)
                c = SimpleNamespace(commit='a' * 40, identity={'source_commit': 'a' * 40},
                    script=b'exact runner', installer=b'exact installer',
                    ag=SimpleNamespace(d=SimpleNamespace(attempt=attempt, save=save,
                        original_git_state=lambda _: {'dirty': ['retained.lean']},
                        write_frozen=denied_frozen_write)))
                with patch.object(geometry, 'ROOT', root), patch.object(geometry, 'INSTALL_ROOT', root):
                    with contextlib.redirect_stdout(io.StringIO()):
                        code = geometry.dispatch(c, installation=install)
                run = root / ('a' * 40) / 'runs/attempt-00000'
                result_name = 'SOURCE_INSTALL_RESULT.json' if install else 'RESULT.json'
                row = json.loads((run / result_name).read_text())
                self.assertEqual(code, 3)
                self.assertIs(row['new_owner_accepted'], False)
                self.assertIn('test frozen write refused', row['dispatch_error'])
                self.assertEqual(json.loads((run / 'GIT_BEFORE.json').read_text()),
                                 json.loads((run / 'GIT_AFTER.json').read_text()))


if __name__ == '__main__':
    unittest.main(verbosity=2)
