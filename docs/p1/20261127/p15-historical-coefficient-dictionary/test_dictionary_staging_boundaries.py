"""Local staging boundary checks; test bindings are synthetic and never deployed."""
from pathlib import Path
import copy
import importlib.util
import os
import pprint
import tempfile
import unittest
from unittest.mock import Mock, patch

HERE = Path(__file__).resolve().parent
def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module
s = load('dictionary_formal_stager_test_subject', 'stage_dictionary_formal.py')
b = load('dictionary_formal_bootstrap_test_subject', 'deploy_dictionary_formal.py')


class DictionaryStagingBoundaries(unittest.TestCase):
    def runtime(self):
        return {'canonical_source': s.SOURCE_FP, 'probe_publication': s.AO,
            'probe_job': 'job_' + '0' * 32, 'probe_document': {'bytes': 1, 'sha256': '0' * 64},
            'geometry': {'mode': 'accepted', 'source_commit': s.AN,
                'reader_path': 'docs/p1/20261127/p15-remaining-typei-geometry/run_geometry.py',
                'reader': {'bytes': 1, 'sha256': '1' * 64},
                'readonly_report': {'bytes': 1, 'sha256': '2' * 64}}}

    def bindings(self):
        inputs = self.runtime(); payloads = {}
        for name in s.UNBOUND_ENTRYPOINTS:
            raw = (HERE / name.replace('.py', '.v2.unbound.py')).read_bytes()
            self.assertEqual(s.fp(raw), s.UNBOUND_ENTRYPOINTS[name])
            self.assertEqual(raw.count(b'INPUTS = None\n'), 1)
            assignment = ('INPUTS = ' + pprint.pformat(inputs, sort_dicts=True, width=70) + '\n').encode()
            payloads[name] = raw.replace(b'INPUTS = None\n', assignment)
        return {'source_origin': {'commit': s.AO, 'path': s.ORIGIN, **s.SOURCE_FP},
                'runtime_inputs': inputs, 'entrypoints': {name: s.fp(raw) for name, raw in payloads.items()}}, payloads

    def test_both_unbound_entrypoints_close_before_files_fetch_or_process(self):
        self.assertIsNone(s.INPUTS); self.assertIsNone(b.INPUTS)
        with patch.object(Path, 'read_bytes') as read, patch.object(Path, 'is_file') as stat, \
             patch.object(s.subprocess, 'run') as run, patch.object(s.subprocess, 'check_output') as git:
            for operation in (lambda: s.main(), lambda: s.stage('f' * 40, b''),
                              lambda: b.main(), lambda: b.deploy('f' * 40)):
                with self.assertRaisesRegex(RuntimeError, 'unbound'):
                    operation()
            read.assert_not_called(); stat.assert_not_called(); run.assert_not_called(); git.assert_not_called()

    def test_only_INPUTS_splice_restores_exact_reviewed_v2_bytes(self):
        inputs, payloads = self.bindings()
        with patch.object(s, 'INPUTS', inputs):
            for name, raw in payloads.items():
                s.validate_final_payload(name, raw)
                value, restored = s.inputs_assignment(raw)
                self.assertEqual(value, inputs['runtime_inputs'])
                self.assertEqual(s.fp(restored), s.UNBOUND_ENTRYPOINTS[name])

    def test_changed_code_is_rejected_even_with_matching_new_payload_pin(self):
        inputs, payloads = self.bindings(); name = 'run_dictionary.py'
        changed = payloads[name].replace(b"'new_owner_accepted': False", b"'new_owner_accepted': True", 1)
        self.assertNotEqual(changed, payloads[name]); inputs['entrypoints'][name] = s.fp(changed)
        with patch.object(s, 'INPUTS', inputs), self.assertRaisesRegex(RuntimeError, 'beyond the exact reviewed'):
            s.validate_final_payload(name, changed)

    def test_runner_installer_actual_bindings_must_match(self):
        inputs, payloads = self.bindings(); name = 'install_dictionary_source.py'
        changed = payloads[name].replace(('job_' + '0' * 32).encode(), ('job_' + 'f' * 32).encode())
        inputs['entrypoints'][name] = s.fp(changed)
        with patch.object(s, 'INPUTS', inputs), self.assertRaisesRegex(RuntimeError, 'beyond the exact reviewed'):
            s.validate_final_payload(name, changed)

    def test_dynamic_INPUTS_expression_is_never_executed(self):
        raw = b"INPUTS = __import__('os').system('should-never-run')\n"
        with patch.object(os, 'system') as system:
            with self.assertRaises((ValueError, RuntimeError)):
                s.inputs_assignment(raw)
            system.assert_not_called()

    def test_AO_probe_and_AN_acceptance_publications_cannot_be_reused(self):
        inputs, _ = self.bindings()
        with patch.object(s, 'INPUTS', inputs), patch.object(s, 'gitstate') as observed:
            for commit in (s.AO, s.AN):
                with self.assertRaisesRegex(RuntimeError, 'unique new formal publication'):
                    s.stage(commit, b'')
            observed.assert_not_called()

    def test_put_preserves_existing_bytes_and_refuses_symlink_ancestors(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for n, module in enumerate((s, b)):
                path = root / str(n) / 'entry.py'
                module.put(path, b'original')
                with self.assertRaisesRegex(RuntimeError, 'cannot be overwritten'):
                    module.put(path, b'changed')
                self.assertEqual(path.read_bytes(), b'original')
            real = root / 'real'; real.mkdir(); link = root / 'link'; link.symlink_to(real, target_is_directory=True)
            for module in (s, b):
                with self.assertRaisesRegex(RuntimeError, 'symlink'):
                    module.put(link / 'new/entry.py', b'bytes')
            self.assertFalse((real / 'new').exists())

    def test_bootstrap_rejects_an_unbound_pinned_stager_before_copy_or_execute(self):
        raw = b'INPUTS = None\n'
        inputs = {'probe_publication': b.AO, 'stager': b.fp(raw)}
        with patch.object(b, 'INPUTS', inputs), patch.object(b, 'gitstate', return_value={}), \
             patch.object(b, 'git', return_value=raw), patch.object(b.subprocess, 'run', return_value=Mock(returncode=0)) as run, \
             patch.object(b, 'put') as write:
            with self.assertRaisesRegex(RuntimeError, 'still unbound'):
                b.deploy('f' * 40)
            write.assert_not_called()
            self.assertEqual(run.call_count, 2)  # Mocked fetch and ancestry; no Python stager process.


if __name__ == '__main__':
    unittest.main(verbosity=2)
