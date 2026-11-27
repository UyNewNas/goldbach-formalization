"""New probe boundaries only; no Lean, cloud, original tests or old owner builds."""
from pathlib import Path
from types import SimpleNamespace
import copy
import importlib.util
import json
import os
import tempfile
import unittest
from unittest.mock import Mock, patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('geometry_probe_under_review', HERE / 'probe_geometry.py')
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


class GeometryProbeBoundaries(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        manifest = Path(os.environ.get('P15_GEOMETRY_MANIFEST',
            'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'))
        published = Path(os.environ.get('P15_GEOMETRY_PUBLIC', probe.PUBLIC))
        cls.candidate = Path(os.environ.get('P15_GEOMETRY_SOURCE', probe.SOURCE))
        cls.manifest = json.loads(manifest.read_bytes())
        cls.published = json.loads(published.read_bytes())
        if probe.raw_fp(published.read_bytes()) != probe.PUBLIC_FP:
            raise RuntimeError('original public fixture differs')

    def complete_read(self):
        pub = self.published
        return {
            'status': 'ORIGINAL_TRIMLOG_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION',
            'new_owner_accepted': True, 'normal_or_kernel_commands_executed': 0,
            'identity': {'source_commit': probe.AI},
            'owner': {'binding': pub['owner_binding'], 'audit_id': pub['audit_id'],
                      'owned_count': 4, 'public_count': 4,
                      'full_owned_including_private_generated': True,
                      'only_standard_axioms': True},
            'accepting_run': {'path': pub['original_accepting_run']['path'],
                             'new_owner_accepted': True, 'recompiled_by_check': False}}

    def test_real_141_dependencies_are_inside_original_144(self):
        selected = probe.scope(self.manifest)
        self.assertEqual(len(selected['dependency_sources']), 141)
        self.assertEqual(selected['active_source_count_with_owner'], 142)
        self.assertEqual(selected['unaccepted_P3_dependencies'], [])

    def test_missing_dependency_refuses_scope(self):
        changed = copy.deepcopy(self.manifest)
        changed['project_sources'][probe.IMPORTS[0]]['imports'].append('ImbalancedChen.MissingOriginalProvider')
        with self.assertRaisesRegex(RuntimeError, 'missing project dependency'):
            probe.scope(changed)

    def test_p3_hold_cannot_be_silently_adopted(self):
        changed = copy.deepcopy(self.manifest)
        held = changed['unaccepted_p3_dependencies']
        if isinstance(held, dict):
            held[probe.IMPORTS[0]] = {}
        else:
            held.append(probe.IMPORTS[0])
        with self.assertRaisesRegex(RuntimeError, 'unaccepted P3'):
            probe.scope(changed)

    def test_normal_only_or_partial_audit_is_not_original_acceptance(self):
        report = self.complete_read()
        probe.require_original_acceptance(report, self.published)
        report['owner']['full_owned_including_private_generated'] = False
        with self.assertRaisesRegex(RuntimeError, 'owned declarations'):
            probe.require_original_acceptance(report, self.published)
        report = self.complete_read()
        report['status'] = 'NORMAL_PASS_ONLY'
        with self.assertRaisesRegex(RuntimeError, 'complete read-only'):
            probe.require_original_acceptance(report, self.published)

    def test_original_commit_and_original_run_cannot_be_rebound(self):
        for key in ('commit', 'run'):
            report = self.complete_read()
            if key == 'commit':
                report['identity']['source_commit'] = probe.AJ
            else:
                report['accepting_run']['path'] += '-another-run'
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                probe.require_original_acceptance(report, self.published)

    def test_partial_geometry_artifacts_or_history_stop_recompilation(self):
        slots = {str(i): None for i in range(21)}
        probe.require_fresh_slot(None, slots, [])
        probe.require_fresh_slot(probe.SOURCE_FP, slots, [])
        changed = dict(slots); changed['0'] = {'bytes': 1, 'sha256': 'foreign'}
        with self.assertRaisesRegex(RuntimeError, 'started acceptance history'):
            probe.require_fresh_slot(None, changed, [])
        with self.assertRaisesRegex(RuntimeError, 'started acceptance history'):
            probe.require_fresh_slot(None, slots, ['/old/partial-owner'])

    def test_object_emission_and_dependency_build_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / 'WholeGeometryProbe.lean'
            candidate.write_bytes(self.candidate.read_bytes())
            reader = SimpleNamespace(fp=lambda p: probe.raw_fp(Path(p).read_bytes()))
            clean = {'actual_built_modules': [], 'actual_failed_modules': []}
            probe.require_probe_output(reader, candidate, clean)
            candidate.with_suffix('.olean').write_bytes(b'forbidden probe output')
            with self.assertRaisesRegex(RuntimeError, 'emitted an object'):
                probe.require_probe_output(reader, candidate, clean)
            candidate.with_suffix('.olean').unlink()
            with self.assertRaisesRegex(RuntimeError, 'rebuilt a project module'):
                probe.require_probe_output(reader, candidate,
                    {'actual_built_modules': [probe.IMPORTS[0]], 'actual_failed_modules': []})

    def test_preparation_failure_saves_result_and_attempts_after_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            run_dir = Path(directory) / 'attempt-00000'
            run_dir.mkdir()
            saved = {}
            save = lambda path, data: saved.update({Path(path).name: copy.deepcopy(data)})
            helpers = SimpleNamespace(attempt=lambda parent: run_dir,
                write_frozen=Mock(side_effect=OSError('simulated preparation write failure')), save=save)
            compiler = Mock()
            c = SimpleNamespace(ag=SimpleNamespace(d=helpers, ops=SimpleNamespace(run=compiler)))
            reader = SimpleNamespace(fp=lambda path: None)
            with patch.object(probe, 'PROBE_ROOT', Path(directory) / 'fresh-root'), \
                 patch.object(probe, 'load_original', return_value=(reader, c, b'source', {}, {})), \
                 patch.object(probe, 'snapshot', side_effect=[{'old': 'intact'}, {'old': 'intact'}]) as snap, \
                 patch('builtins.print'):
                status = probe.run(probe.AJ, b'entrypoint')
            self.assertNotEqual(status, 0)
            self.assertEqual(snap.call_count, 2)
            compiler.assert_not_called()
            result = saved['ACTUAL_GEOMETRY_PROBE_RESULT.json']
            self.assertIn('simulated preparation write failure', result['probe_error'])
            self.assertFalse(result['probe_passed'])
            self.assertFalse(result['new_owner_accepted'])
            self.assertFalse(result['typecheck_command_completed'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
