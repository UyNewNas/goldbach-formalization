"""Only new adapter boundaries. Mocked acceptance fixtures are never real receipts."""
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
def module(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value
a = module('dictionary_formal_boundary_subject', 'run_dictionary.py')
i = module('dictionary_installer_boundary_subject', 'install_dictionary_source.py')


class DictionaryFormalBoundaries(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.selected = json.loads(Path(os.environ.get('P15_DICT_SCOPE',
            str(HERE.parent / 'probe/DEPENDENCY_SCOPE.json'))).read_bytes())
        cls.source = Path(os.environ.get('P15_DICT_SOURCE',
            str(HERE.parent / 'new/P1OriginalHistoricalCoefficientDictionary.lean'))).read_bytes()
        if a.raw_fp(cls.source) != a.SOURCE_FP:
            raise RuntimeError('frozen source fixture differs')

    def inputs(self):
        # Shape-only local fixture, used exclusively with mocked I/O or temp files.
        return {'canonical_source': a.SOURCE_FP, 'probe_publication': a.AM,
            'probe_job': 'job_' + '0' * 32, 'probe_document': {'bytes': 1, 'sha256': '0' * 64},
            'geometry': {'mode': 'unaccepted', 'source': None}}

    def test_unbound_runner_entrypoints_perform_no_file_or_process_io(self):
        self.assertIsNone(a.INPUTS)
        calls = [lambda: a.main(), lambda: a.load('f' * 40, b'code'),
                 lambda: a.prepare(None), lambda: a.dispatch(None), lambda: a.worker(None, None)]
        with patch.object(a.subprocess, 'check_output') as git, patch.object(a.subprocess, 'run') as run, \
             patch.object(Path, 'read_bytes') as read, patch.object(Path, 'is_file') as stat:
            for call in calls:
                with self.assertRaisesRegex(RuntimeError, 'INPUTS are unbound'):
                    call()
            git.assert_not_called(); run.assert_not_called(); read.assert_not_called(); stat.assert_not_called()

    def test_unbound_installer_blocks_even_adapter_lookup(self):
        self.assertIsNone(i.INPUTS)
        with patch.object(i.subprocess, 'check_output') as git, patch.object(i.subprocess, 'run') as run, \
             patch.object(Path, 'read_bytes') as read, patch.object(os, 'open') as write:
            for call in (lambda: i.main(), lambda: i.load('f' * 40, b'code'),
                         lambda: i.worker(None, None, None), lambda: i.install_exact(None, None, None, None)):
                with self.assertRaisesRegex(RuntimeError, 'INPUTS are unbound'):
                    call()
            git.assert_not_called(); run.assert_not_called(); read.assert_not_called(); write.assert_not_called()

    def test_incomplete_geometry_binding_is_rejected_before_installer_git(self):
        bad = self.inputs(); bad['geometry'] = {'mode': 'accepted'}
        with patch.object(i, 'INPUTS', bad), patch.object(i.subprocess, 'check_output') as git:
            with self.assertRaisesRegex(RuntimeError, 'Geometry preservation INPUTS are unbound'):
                i.load('f' * 40, b'code')
            git.assert_not_called()
        with self.assertRaisesRegex(RuntimeError, 'Geometry reader/report identity is unbound'):
            a.validate_inputs(bad)

    def inventory_context(self):
        active = set(self.selected['dependency_sources'])
        paths = lambda m: [m + '/artifact-' + str(n) for n in range(21)]
        inventory = {m: {p: None for p in paths(m)} for m in active}
        c = SimpleNamespace(selected=self.selected, g=SimpleNamespace(artifact_paths=paths))
        state = SimpleNamespace(retained=SimpleNamespace(direct=SimpleNamespace(
            baseline={'preserved_dependency_artifacts': inventory})))
        return c, state, inventory

    def test_actual_D288_requires_every_slot_outside_AG144(self):
        c, state, inventory = self.inventory_context()
        bound = a.dependency_inventory(c, state)
        self.assertEqual(len(bound), 288); self.assertEqual(sum(map(len, bound.values())), 6048)
        outside = self.selected['dependencies_outside_original_AG'][0]
        del inventory[outside]
        with self.assertRaisesRegex(RuntimeError, 'complete original D288'):
            a.dependency_inventory(c, state)

    def test_two_pin_maps_and_geometry_dependency_cannot_substitute(self):
        c, state, inventory = self.inventory_context()
        first = next(iter(inventory)); inventory[first] = dict(list(inventory[first].items())[:2])
        with self.assertRaisesRegex(RuntimeError, 'two-slot pins'):
            a.dependency_inventory(c, state)
        c, state, inventory = self.inventory_context()
        c.selected = copy.deepcopy(c.selected)
        c.selected['dependency_sources'][a.GEOMETRY] = {}
        with self.assertRaisesRegex(RuntimeError, 'complete original D288'):
            a.dependency_inventory(c, state)

    def test_installer_cannot_replace_foreign_source_or_follow_symlink(self):
        inputs = self.inputs()
        with tempfile.TemporaryDirectory() as directory, patch.object(a, 'INPUTS', inputs), patch.object(i, 'INPUTS', inputs):
            path = Path(directory) / 'Dictionary.lean'; path.write_bytes(b'foreign')
            with self.assertRaisesRegex(RuntimeError, 'foreign canonical source'):
                i.install_exact(a, path, self.source, None)
            self.assertEqual(path.read_bytes(), b'foreign')
            target = Path(directory) / 'real'; target.mkdir()
            link = Path(directory) / 'link'; link.symlink_to(target, target_is_directory=True)
            with self.assertRaisesRegex(RuntimeError, 'symlink'):
                i.install_exact(a, link / 'Dictionary.lean', self.source, None)
            self.assertFalse((target / 'Dictionary.lean').exists())

    def test_exact_source_installation_does_not_allow_started_owner(self):
        inputs = self.inputs()
        with tempfile.TemporaryDirectory() as directory, patch.object(a, 'INPUTS', inputs), patch.object(i, 'INPUTS', inputs):
            path = Path(directory) / 'Dictionary.lean'
            self.assertEqual(i.install_exact(a, path, self.source, None), 'EXCLUSIVE_NEW_CANONICAL_SOURCE')
            self.assertEqual(i.install_exact(a, path, self.source, None), 'IDENTICAL_SOURCE_BEFORE_OWNER_START')
            with self.assertRaisesRegex(RuntimeError, 'started owner history'):
                a.require_new_slot(a.fp(path), {str(n): None for n in range(21)}, ['/partial/owner'], installed=True)

    def test_started_or_foreign_dictionary_owner_is_not_recompiled(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(a, 'ROOT', Path(directory)):
            commit = '1' * 40; foreign = Path(directory) / ('2' * 40) / a.TARGET
            c = SimpleNamespace(commit=commit)
            with patch.object(a, 'owner_history', return_value=[foreign]):
                with self.assertRaisesRegex(RuntimeError, 'foreign Dictionary owner history'):
                    a.new_owner_state(c, None)
            own = Path(directory) / commit / a.TARGET; own.mkdir(parents=True)
            with patch.object(a, 'owner_history', return_value=[own]):
                with self.assertRaisesRegex(RuntimeError, 'partial Dictionary owner'):
                    a.new_owner_state(c, None)

    def test_complete_existing_owner_takes_only_original_readers(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(a, 'ROOT', Path(directory)):
            commit = '1' * 40; own = Path(directory) / commit / a.TARGET
            normal = own / 'normal' / a.TARGET / 'NORMAL_PASS.json'; normal.parent.mkdir(parents=True); normal.write_text('{}')
            existing = {'status': 'BOUND_CURRENT_NORMAL_RECEIPT'}
            old = SimpleNamespace(existing_owner=Mock(return_value=existing),
                require_completed_existing_owner=Mock(), run_owner=Mock())
            c = SimpleNamespace(commit=commit, g=old, ag=object())
            with patch.object(a, 'owner_history', return_value=[own]):
                self.assertEqual(a.new_owner_state(c, object()), existing)
            old.require_completed_existing_owner.assert_called_once(); old.run_owner.assert_not_called()

    def test_unaccepted_geometry_mode_cannot_skip_new_artifacts_or_history(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(a, 'ROOT', Path(directory)), \
             patch.object(a, 'PROJECT', Path(directory)), patch.object(a, 'GEOMETRY_PROBE_ROOT', Path(directory) / 'no-probes'), \
             patch.object(a, 'INPUTS', self.inputs()):
            paths = [str(n) for n in range(21)]; artifacts = {p: None for p in paths}
            c = SimpleNamespace(geometry_reader=None, g=SimpleNamespace(
                module_artifacts=lambda s, m: artifacts, artifact_paths=lambda m: paths), ag=object())
            observation = a.geometry_snapshot(c)
            self.assertFalse(observation['is_dictionary_dependency'])
            artifacts['0'] = {'bytes': 1, 'sha256': '0' * 64}
            with self.assertRaisesRegex(RuntimeError, 'Geometry gained accepted or partial'):
                a.geometry_snapshot(c)
            artifacts['0'] = None
            (Path(directory) / ('3' * 40) / a.GEOMETRY).mkdir(parents=True)
            with self.assertRaisesRegex(RuntimeError, 'Geometry gained accepted or partial'):
                a.geometry_snapshot(c)

    def test_geometry_normal_only_reader_is_not_full_acceptance(self):
        inputs = self.inputs(); inputs['geometry'] = {'mode': 'accepted', 'source_commit': '3' * 40}
        with tempfile.TemporaryDirectory() as directory, patch.object(a, 'ROOT', Path(directory)), \
             patch.object(a, 'PROJECT', Path(directory)), patch.object(a, 'GEOMETRY_PROBE_ROOT', Path(directory) / 'no-probes'), \
             patch.object(a, 'INPUTS', inputs):
            reader = SimpleNamespace(check=Mock(return_value={'status': 'NORMAL_PASS_ONLY'}))
            paths = [str(n) for n in range(21)]
            c = SimpleNamespace(geometry_reader=(reader, object()), g=SimpleNamespace(
                module_artifacts=lambda s, m: {p: None for p in paths}, artifact_paths=lambda m: paths), ag=object())
            with self.assertRaisesRegex(RuntimeError, 'complete read-only acceptance identity'):
                a.geometry_snapshot(c)
            reader.check.assert_called_once()


if __name__ == '__main__':
    unittest.main(verbosity=2)
