"""Only the repaired-source/v2/old-failure delta; no old suite or Lean runs."""
from pathlib import Path
from types import SimpleNamespace
import copy
import importlib.util
import unittest
from unittest.mock import Mock, patch

HERE = Path(__file__).resolve().parent
def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module
a = load('repaired_dictionary_formal_delta', 'run_dictionary.py')
i = load('repaired_dictionary_installer_delta', 'install_dictionary_source.py')


class RepairedFormalDelta(unittest.TestCase):
    def inputs(self):
        # Shape-only local test data. Neither production INPUTS is modified.
        return {'canonical_source': a.SOURCE_FP, 'probe_publication': '0' * 40,
            'probe_job': 'job_' + '0' * 32, 'probe_document': {'bytes': 1, 'sha256': '0' * 64},
            'geometry': {'mode': 'unaccepted', 'source': None}}

    def header(self):
        # Synthetic positive header only, with no fabricated command/log/receipt.
        # Every test mutates a required identity and must stop before any I/O.
        return {'schema': 'p15_historical_coefficient_dictionary_whole_no_output_probe_v2',
            'publication': '0' * 40,
            'source_origin': {'commit': '0' * 40, 'path': a.ORIGIN, **a.SOURCE_FP},
            'original_dictionary_source': {'commit': a.AK, 'path': a.ORIGINAL_ORIGIN, **a.ORIGINAL_SOURCE_FP},
            'proof_repair': 'split_original_moebius_sign_ite_after_negation_simp',
            'original_failed_probe': {'publication': a.AM, 'compiler_job': a.FAILED_PROBE_JOB, **a.FAILED_PROBE_FP},
            'entrypoint': {'path': a.PROBE_SCRIPT, **a.PROBE_SCRIPT_FP},
            'original_AI_acceptance_commit': a.AI, 'original_AG_acceptance_commit': a.AG,
            'scope': {}, 'probe_passed': True, 'exit_code': 0, 'preservation_passed': True,
            'typecheck_command_completed': True, 'original_dependency_acceptance_preparation_completed': True,
            'Lean_typecheck_commands': 1, 'whole_original_module_submitted': True,
            'output_object_requested': False, 'existing_project_modules_rebuilt': [],
            'original_serializer_and_guard_used': True, 'normal_or_kernel_acceptance_claimed': False,
            'new_owner_accepted': False, 'whole_P1_5_complete': False}

    def test_unbound_state_and_rejected_AM_or_old_source_inputs(self):
        self.assertIsNone(a.INPUTS); self.assertIsNone(i.INPUTS)
        for key, value in [('probe_publication', a.AM), ('canonical_source', a.ORIGINAL_SOURCE_FP)]:
            inputs = self.inputs(); inputs[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, 'unbound'):
                a.validate_inputs(inputs)
            with patch.object(i, 'INPUTS', inputs), patch.object(i.subprocess, 'check_output') as command:
                with self.assertRaisesRegex(RuntimeError, 'unbound'):
                    i.load('f' * 40, b'code')
                command.assert_not_called()

    def test_v1_or_old_source_cannot_pass_v2_identity_gate(self):
        for kind in ('v1', 'old_source'):
            row = self.header()
            if kind == 'v1': row['schema'] = 'p15_historical_coefficient_dictionary_whole_no_output_probe_v1'
            else: row['source_origin'] = {'commit': a.AK, 'path': a.ORIGINAL_ORIGIN, **a.ORIGINAL_SOURCE_FP}
            with patch.object(a, 'INPUTS', self.inputs()), patch.object(a, 'fp') as stat:
                with self.subTest(kind=kind), self.assertRaisesRegex(RuntimeError, 'actual whole-source probe'):
                    a.read_probe(SimpleNamespace(probe=row, selected={}), None)
                stat.assert_not_called()

    def test_original_AM_failure_cannot_be_rebound_to_repaired_source(self):
        row = self.header(); row['original_failed_probe']['sha256'] = a.SOURCE_FP['sha256']
        with patch.object(a, 'INPUTS', self.inputs()), patch.object(a, 'fp') as stat:
            with self.assertRaisesRegex(RuntimeError, 'actual whole-source probe'):
                a.read_probe(SimpleNamespace(probe=row, selected={}), None)
            stat.assert_not_called()

    def test_changed_original_AM_tree_fails_even_if_other_contexts_match(self):
        tree = {'new-probe': 'unchanged'}
        reader = SimpleNamespace(tree_inventory=Mock(return_value=tree))
        ai = SimpleNamespace(readers={'ag': reader})
        failed = Mock(return_value={'original-AM': 'changed'})
        c = SimpleNamespace(base=SimpleNamespace(unchanged_old=Mock()), ai=ai, selected={},
            probe_api=SimpleNamespace(retained_snapshot=Mock(return_value='D288/W58'), failed_probe_snapshot=failed))
        state = SimpleNamespace(old=object(), ai='AI', dependency_context='D288/W58',
            retained=SimpleNamespace(evidence_folders=[]), supplier_trees={}, geometry='Geometry',
            probe={'path': '/actual/new/probe', 'tree': tree, 'original_AM_failed_probe': {'original-AM': 'unchanged'}})
        with patch.object(a, 'INPUTS', self.inputs()), patch.object(a, 'ai_snapshot', return_value='AI'), \
             patch.object(a, 'geometry_snapshot', return_value='Geometry'):
            with self.assertRaisesRegex(RuntimeError, 'original AI, D288/W58'):
                a.unchanged(c, state)
        failed.assert_called_once_with(ai, {})


if __name__ == '__main__':
    unittest.main(verbosity=2)
