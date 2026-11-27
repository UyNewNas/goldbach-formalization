"""Local boundary checks for the new probe; no Lean or cloud operations."""
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
spec = importlib.util.spec_from_file_location('dictionary_probe_under_review', HERE / 'probe_dictionary.py')
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
stage_spec = importlib.util.spec_from_file_location('dictionary_stager_under_review', HERE / 'stage_dictionary.py')
stager = importlib.util.module_from_spec(stage_spec)
stage_spec.loader.exec_module(stager)


class DictionaryProbeBoundaries(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        def read(name, default):
            return json.loads(Path(os.environ.get(name, default)).read_bytes())
        cls.manifest = read('P15_DICTIONARY_MANIFEST',
            'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json')
        cls.initial = read('P15_DICTIONARY_INITIAL4_GRAPH',
            'docs/p1/20261125/p15-singleton-proper-power/SOURCE_CLOSURE.json')
        cls.atlas = read('P15_DICTIONARY_ATLAS_GRAPH',
            'docs/p1/20261125/p15-atlas-current-context-integration/ATLAS10_MANIFEST.json')
        public_path = Path(os.environ.get('P15_DICTIONARY_PUBLIC', probe.PUBLIC))
        cls.public = json.loads(public_path.read_bytes())
        cls.source = Path(os.environ.get('P15_DICTIONARY_SOURCE', probe.ORIGIN)).read_bytes()
        if probe.raw_fp(public_path.read_bytes()) != probe.PUBLIC_FP or probe.raw_fp(cls.source) != probe.SOURCE_FP:
            raise RuntimeError('original public receipt or frozen Lean fixture differs')

    def selected(self, manifest=None, initial=None, atlas=None):
        return probe.scope(manifest or self.manifest, initial or self.initial, atlas or self.atlas)

    def complete_read(self):
        pub = self.public
        return {'status': 'ORIGINAL_TRIMLOG_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION',
                'new_owner_accepted': True, 'normal_or_kernel_commands_executed': 0,
                'identity': {'source_commit': probe.AI},
                'owner': {'binding': pub['owner_binding'], 'audit_id': pub['audit_id'],
                    'owned_count': 4, 'public_count': 4, 'full_owned_including_private_generated': True,
                    'only_standard_axioms': True},
                'accepting_run': {'path': pub['original_accepting_run']['path'],
                    'new_owner_accepted': True, 'recompiled_by_check': False}}

    def test_actual_288_initial4_closure_and_separate_witness(self):
        selected = self.selected()
        dependencies = set(selected['dependency_sources'])
        witness = selected['separate_original_evidence_scope']
        self.assertEqual(len(dependencies), 288)
        self.assertEqual(selected['fixed_dependency_witness_counts'], probe.FIXED_WITNESS_COUNTS)
        self.assertEqual(len(selected['dependencies_outside_original_AG']), 180)
        self.assertEqual(len(witness['sources']), 58)
        self.assertEqual(set(witness['sources']) - dependencies, set(witness['outside_dictionary']))
        self.assertEqual(len(witness['outside_dictionary']), 11)
        self.assertNotIn(probe.WITNESS, dependencies)

    def test_file_presence_does_not_replace_accepted_fixed_provenance(self):
        changed = copy.deepcopy(self.manifest)
        active = self.selected()['dependency_sources']
        dependency = next(m for m in active if m in changed['fixed_dependencies'])
        del changed['fixed_dependencies'][dependency]
        self.assertIn(dependency, changed['project_sources'])
        with self.assertRaisesRegex(RuntimeError, 'acceptance classification'):
            self.selected(manifest=changed)

    def test_observation_only_cannot_replace_original_normal_witness(self):
        changed = copy.deepcopy(self.manifest)
        dependency = next(m for m in self.selected()['dependency_sources'] if m in changed['fixed_dependencies'])
        changed['fixed_dependencies'][dependency] = {'kind': 'retained_object_observation',
            'observation_key': dependency, 'required_extensions': ['.olean', '.trace']}
        with self.assertRaisesRegex(RuntimeError, 'accepted-normal witness'):
            self.selected(manifest=changed)

    def test_source_or_original_accepting_commit_drift_is_rejected(self):
        changed = copy.deepcopy(self.manifest)
        changed['project_sources'][probe.PROJECT_IMPORTS[0]]['sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'original 288-source context'):
            self.selected(manifest=changed)
        changed = copy.deepcopy(self.manifest)
        changed['accepted_supplier_groups']['initial4']['source_commit'] = probe.AK
        with self.assertRaisesRegex(RuntimeError, 'accepting commits'):
            self.selected(manifest=changed)

    def test_p3_hold_and_missing_dependency_cannot_enter_scope(self):
        changed = copy.deepcopy(self.manifest)
        held = changed['unaccepted_p3_dependencies']
        if isinstance(held, dict):
            held[probe.PROJECT_IMPORTS[0]] = {}
        else:
            held.append(probe.PROJECT_IMPORTS[0])
        with self.assertRaisesRegex(RuntimeError, 'unaccepted P3'):
            self.selected(manifest=changed)
        changed = copy.deepcopy(self.manifest)
        changed['project_sources'][probe.PROJECT_IMPORTS[0]]['imports'].append('ImbalancedChen.AbsentProvider')
        with self.assertRaisesRegex(RuntimeError, 'missing project dependency'):
            self.selected(manifest=changed)

    def test_atlas_witness_source_cannot_be_silently_substituted(self):
        changed = copy.deepcopy(self.atlas)
        changed['project_sources'][probe.WITNESS]['sha256'] = 'f' * 64
        with self.assertRaisesRegex(RuntimeError, 'separate atlas witness'):
            self.selected(atlas=changed)

    def test_full_6048_slots_are_required_including_outside_ag(self):
        selected = self.selected()
        active = set(selected['dependency_sources'])
        snapshot = {'selected_live_sources': {m: 'bound' for m in active},
                    'preserved_dependency_artifacts': {m: {str(i): None for i in range(21)} for m in active}}
        probe.require_snapshot_scope(snapshot, active, 288)
        outside = selected['dependencies_outside_original_AG'][0]
        del snapshot['preserved_dependency_artifacts'][outside]
        with self.assertRaisesRegex(RuntimeError, 'protection scope is incomplete'):
            probe.require_snapshot_scope(snapshot, active, 288)
        snapshot['preserved_dependency_artifacts'][outside] = {str(i): None for i in range(20)}
        with self.assertRaisesRegex(RuntimeError, 'protection scope is incomplete'):
            probe.require_snapshot_scope(snapshot, active, 288)

    def test_partial_or_rebound_ai_receipt_is_not_acceptance(self):
        valid = self.complete_read()
        probe.require_original_acceptance(valid, self.public)
        for kind in ('normal_only', 'no_private', 'rebound', 'different_run'):
            changed = copy.deepcopy(valid)
            if kind == 'normal_only': changed['status'] = 'NORMAL_PASS_ONLY'
            if kind == 'no_private': changed['owner']['full_owned_including_private_generated'] = False
            if kind == 'rebound': changed['identity']['source_commit'] = probe.AK
            if kind == 'different_run': changed['accepting_run']['path'] += '-different'
            with self.subTest(kind=kind), self.assertRaises(RuntimeError):
                probe.require_original_acceptance(changed, self.public)

    def test_partial_dictionary_artifacts_source_or_history_prevent_recompilation(self):
        slots = {str(i): None for i in range(21)}
        probe.require_fresh_slot(None, slots, [])
        with self.assertRaisesRegex(RuntimeError, 'already installed'):
            probe.require_fresh_slot(probe.SOURCE_FP, slots, [])
        changed = dict(slots); changed['0'] = {'bytes': 1, 'sha256': 'foreign'}
        with self.assertRaisesRegex(RuntimeError, 'started acceptance history'):
            probe.require_fresh_slot(None, changed, [])
        with self.assertRaisesRegex(RuntimeError, 'started acceptance history'):
            probe.require_fresh_slot(None, slots, ['/old/partial-owner'])

    def test_object_output_and_dependency_build_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / 'WholeDictionaryProbe.lean'
            candidate.write_bytes(self.source)
            reader = SimpleNamespace(fp=lambda p: probe.raw_fp(Path(p).read_bytes()))
            clean = {'actual_built_modules': [], 'actual_failed_modules': []}
            probe.require_probe_output(reader, candidate, clean)
            candidate.with_suffix('.olean').write_bytes(b'forbidden')
            with self.assertRaisesRegex(RuntimeError, 'emitted an object'):
                probe.require_probe_output(reader, candidate, clean)
            candidate.with_suffix('.olean').unlink()
            with self.assertRaisesRegex(RuntimeError, 'project build'):
                probe.require_probe_output(reader, candidate,
                    {'actual_built_modules': [probe.PROJECT_IMPORTS[0]], 'actual_failed_modules': []})

    def test_readiness_includes_external_import_and_refuses_any_build(self):
        command = Mock(return_value={'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': []})
        c = SimpleNamespace(ag=SimpleNamespace(h=SimpleNamespace(guard=lambda lane, argv: argv,
            serialize=lambda lane, path, argv: argv), ops=SimpleNamespace(run=command)))
        probe.direct_import_readiness(c, Path('/probe'))
        argv = command.call_args.args[2]
        self.assertEqual(argv, ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in probe.IMPORTS])
        command.return_value['actual_built_modules'] = [probe.PROJECT_IMPORTS[0]]
        with self.assertRaisesRegex(RuntimeError, 'NO_REBUILD_ALLOWED'):
            probe.direct_import_readiness(c, Path('/probe'))

    def exercise_run(self, directory, write_failure=False, changed_after=False, readiness_failure=False,
                     dependency_failure=False):
        run_dir = Path(directory) / 'attempt-00000'
        run_dir.mkdir()
        saved = {}
        def save(path, data):
            saved[Path(path).name] = copy.deepcopy(data)
            Path(path).write_text(json.dumps(data))
        def fp(path):
            path = Path(path)
            return probe.raw_fp(path.read_bytes()) if path.is_file() else None
        def command(directory, name, argv, **kwargs):
            log = run_dir / (name + '.log'); log.write_text('whole-source success fixture\n')
            return {'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': [], 'log': str(log)}
        compiler = Mock(side_effect=command)
        writer = Mock(side_effect=OSError('simulated preparation write failure')) if write_failure else (
            lambda path, raw: Path(path).write_bytes(raw))
        helpers = SimpleNamespace(attempt=lambda parent: run_dir, write_frozen=writer, save=save)
        c = SimpleNamespace(ag=SimpleNamespace(d=helpers, ops=SimpleNamespace(run=compiler),
            h=SimpleNamespace(guard=lambda lane, argv: argv, serialize=lambda lane, path, argv: argv)))
        reader = SimpleNamespace(fp=fp)
        after = {'preserved': 'outside-AG object changed'} if changed_after else {'preserved': 'intact'}
        with patch.object(probe, 'PROBE_ROOT', Path(directory) / 'fresh-root'), \
             patch.object(probe, 'load_original', return_value=(reader, c, self.source, {}, {}, {})), \
             patch.object(probe, 'prepare_dependency_scopes', side_effect=(RuntimeError('stale original dependency receipt')
                 if dependency_failure else None), return_value=object()), \
             patch.object(probe, 'retained_snapshot', return_value={'validated': 'original receipts'}), \
             patch.object(probe, 'snapshot', side_effect=[{'preserved': 'intact'}, after]) as snap, \
             patch.object(probe, 'direct_import_readiness', side_effect=(RuntimeError('missing cached external import')
                 if readiness_failure else None), return_value={'exit_code': 0}), \
             patch('builtins.print'):
            status = probe.run(probe.AK, b'entrypoint')
        self.assertEqual(snap.call_count, 2)
        return status, saved['ACTUAL_DICTIONARY_PROBE_RESULT.json'], compiler

    def test_preparation_failure_retains_after_check_and_does_not_run_lean(self):
        with tempfile.TemporaryDirectory() as directory:
            status, result, compiler = self.exercise_run(directory, write_failure=True)
        self.assertNotEqual(status, 0)
        compiler.assert_not_called()
        self.assertIn('simulated preparation write failure', result['probe_error'])
        self.assertFalse(result['probe_passed'])
        self.assertEqual(result['Lean_typecheck_commands'], 0)

    def test_missing_cache_stops_before_whole_lean_command(self):
        with tempfile.TemporaryDirectory() as directory:
            status, result, compiler = self.exercise_run(directory, readiness_failure=True)
        self.assertNotEqual(status, 0)
        compiler.assert_not_called()
        self.assertFalse(result['probe_passed'])
        self.assertEqual(result['Lean_typecheck_commands'], 0)

    def test_dependency_preparation_failure_saves_result_and_after_observation(self):
        with tempfile.TemporaryDirectory() as directory:
            status, result, compiler = self.exercise_run(directory, dependency_failure=True)
            after_path = Path(directory) / 'attempt-00000/CONTEXT_AFTER.json'
            self.assertTrue(after_path.is_file())
            self.assertIsNone(json.loads(after_path.read_text())['original_acceptance'])
        self.assertNotEqual(status, 0)
        compiler.assert_not_called()
        self.assertIn('stale original dependency receipt', result['probe_error'])
        self.assertFalse(result['original_dependency_acceptance_preparation_completed'])
        self.assertFalse(result['probe_passed'])
        self.assertFalse(result['new_owner_accepted'])
        self.assertEqual(result['Lean_typecheck_commands'], 0)
        self.assertTrue(result['preservation_passed'])

    def test_successful_lean_with_changed_dependency_is_not_a_success(self):
        with tempfile.TemporaryDirectory() as directory:
            status, result, compiler = self.exercise_run(directory, changed_after=True)
        self.assertNotEqual(status, 0)
        self.assertEqual(result['exit_code'], 0)
        self.assertEqual(compiler.call_count, 1)
        self.assertFalse(result['preservation_passed'])
        self.assertFalse(result['probe_passed'])
        self.assertIn('changed', result['preservation_error'])

    def test_probe_success_never_claims_normal_kernel_or_p15_acceptance(self):
        with tempfile.TemporaryDirectory() as directory:
            status, result, compiler = self.exercise_run(directory)
        self.assertEqual(status, 0)
        self.assertTrue(result['probe_passed'])
        self.assertEqual(compiler.call_count, 1)
        self.assertEqual(result['Lean_typecheck_commands'], 1)
        self.assertFalse(result['new_owner_accepted'])
        self.assertFalse(result['normal_or_kernel_acceptance_claimed'])
        self.assertFalse(result['whole_P1_5_complete'])

    def test_stager_pins_the_actual_probe_and_frozen_source(self):
        self.assertEqual(stager.fp((HERE / 'probe_dictionary.py').read_bytes()), stager.SCRIPT_FP)
        self.assertEqual(stager.fp(self.source), stager.SOURCE_FP)
        self.assertEqual(stager.SOURCE_FP, probe.SOURCE_FP)

    def test_stager_refuses_to_replace_existing_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / 'published-entrypoints/probe_dictionary.py'
            stager.put(destination, b'original')
            stager.put(destination, b'original')
            with self.assertRaisesRegex(RuntimeError, 'different existing staging file'):
                stager.put(destination, b'replacement')
            self.assertEqual(destination.read_bytes(), b'original')

    def test_stager_does_not_create_directories_through_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actual = root / 'actual'; actual.mkdir()
            link = root / 'linked'; link.symlink_to(actual, target_is_directory=True)
            with self.assertRaisesRegex(RuntimeError, 'traverses a symlink'):
                stager.put(link / 'new/probe_dictionary.py', b'bytes')
            self.assertFalse((actual / 'new').exists())

    def test_stager_rejects_source_substitution_before_writing(self):
        raw = (HERE / 'probe_dictionary.py').read_bytes()
        def git(*argv):
            return raw if argv[-1].endswith(':' + stager.SCRIPT) else b'wrong Lean source'
        with patch.object(stager, 'gitstate', return_value={'head': 'unchanged'}), \
             patch.object(stager, 'git', side_effect=git), \
             patch.object(stager.subprocess, 'run', return_value=SimpleNamespace(returncode=0)), \
             patch.object(stager, 'put') as write:
            with self.assertRaisesRegex(RuntimeError, 'frozen AK dictionary source differs'):
                stager.stage(probe.AK)
        write.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
