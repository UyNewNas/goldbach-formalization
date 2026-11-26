#!/usr/bin/env python3
"""Dormant Cell01 v2 provenance checks; no successful v6 receipt is fabricated."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import runpy
import sys
import unittest

HERE = Path(__file__).resolve().parent
DRIVER = Path(sys.argv.pop(1)) if len(sys.argv) > 1 and sys.argv[1].endswith('.py') else HERE / 'run_canonical_cell01_v2.py'
old_argv = sys.argv[:]
sys.argv = [str(HERE / 'test_canonical_cell01.py'), str(DRIVER)]
try:
    BASE = runpy.run_path(str(HERE / 'test_canonical_cell01.py'))
finally:
    sys.argv = old_argv
NS, ROOT = BASE['NS'], BASE['ROOT']
CanonicalCell01Preparation = BASE['CanonicalCell01Preparation']
ACTUAL005_PATH = HERE.parent / 'consumer-attempt005/RESULT.json'
ACTUAL005 = json.loads(ACTUAL005_PATH.read_text())
assert hashlib.sha256(ACTUAL005_PATH.read_bytes()).hexdigest() == 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88'


class FourConsumerProvenance(unittest.TestCase):
    def test_expected_branch_is_actual_v6_publication_and_four_owner_scope(self):
        self.assertEqual(NS['CELL00_PUBLICATION'], '4653b261828f127ba0b5082eaf1106a3fea09d46')
        self.assertEqual(NS['CELL00_RUNNER_SHA256'], '064fa8414660f7036b51bf6bf336f1aef168913dca5722cd4050b9d005174f7a')
        self.assertEqual(str(NS['CELL00_RESULT']), '/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-four-consumers-attempt006/RESULT.json')
        self.assertEqual(NS['CELL00_MODULES'], ACTUAL005['module_order'][1:])
        self.assertEqual(NS['PREVIOUS_COMMIT'], NS['CELL00_PUBLICATION'])
        self.assertIsNone(NS['CELL00_RESULT_SHA256'])
        self.assertIs(NS['CELL00_ARTIFACTS_REVIEWED'], False)

    def test_actual_failed005_is_rejected_as_workflow_prerequisite(self):
        canonical, historical = BASE['canonical_evidence']()
        with self.assertRaisesRegex(RuntimeError, 'Cell00'):
            NS['validate_workflow_receipts'](ACTUAL005, canonical, historical)
        self.assertIs(ACTUAL005['accepted'], False)
        self.assertIs(ACTUAL005['modules']['ImbalancedChen.P2Saving16Cell00Decoded']['accepted'], True)

    def test_relabelled_failed005_is_still_rejected(self):
        forged = copy.deepcopy(ACTUAL005)
        forged.update(schema='p25-cell00-four-consumers-strict-v6', status='ORIGINAL_CELL00_FOUR_CONSUMERS_ACCEPTED',
                      accepted=True, publication_commit=NS['CELL00_PUBLICATION'])
        canonical, historical = BASE['canonical_evidence']()
        with self.assertRaisesRegex(RuntimeError, 'Cell00'):
            NS['validate_workflow_receipts'](forged, canonical, historical)

    def test_actual_failed_history_uses_exact_published_existing_verifiers(self):
        self.assertIn('CELL00_DRIVER', NS)
        path = ROOT / NS['CELL00_DRIVER']
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), NS['CELL00_RUNNER_SHA256'])
        helpers = runpy.run_path(str(path))
        disk = json.loads((HERE.parent / 'consumer-attempt004/RESULT.json').read_text())
        helpers['validate_failed_consumer'](disk)
        helpers['validate_failed_parse'](ACTUAL005, disk)
        self.assertEqual(NS['PREVIOUS_CONSUMER_SHA256'], hashlib.sha256(ACTUAL005_PATH.read_bytes()).hexdigest())

    def test_no_alternative_cell01_proof_or_dependency_path_is_added(self):
        old = {node.name: node for node in ast.parse((HERE / 'run_canonical_cell01.py').read_text()).body if isinstance(node, ast.FunctionDef)}
        new = {node.name: node for node in ast.parse(DRIVER.read_text()).body if isinstance(node, ast.FunctionDef)}
        self.assertEqual(set(old), set(new))
        self.assertEqual({name for name in old if ast.dump(old[name]) != ast.dump(new[name])},
                         {'validate_workflow_receipts', 'main'})
        for name in ['source_graphs', 'validate_dependencies', 'run_stage', 'copy_exact',
                     'qualify_external_context', 'recheck_external_context', 'frozen_snapshot']:
            self.assertEqual(ast.dump(old[name]), ast.dump(new[name]), name)
        self.assertEqual(NS['FRESH_MODULES'], BASE['NS']['FRESH_MODULES'])
        self.assertEqual(NS['INPUT_OBJECT_SHA256'], '72488821ccb01dec90188d2f09b0e3a73c0087b54c6c4bae4410a109b6f82f91')

    def test_future_receipt_failure_blocks_workflow_before_source_or_gate_work(self):
        main = next(node for node in ast.parse(DRIVER.read_text()).body if isinstance(node, ast.FunctionDef) and node.name == 'main')
        self.assertEqual(main.body[0].value.func.id, 'require_workflow_ready')
        self.assertIsNone(NS['CELL00_RESULT_SHA256'])
        self.assertIs(NS['CELL00_ARTIFACTS_REVIEWED'], False)
        self.assertEqual(NS['ATTEMPT'], '.lake/diagnostic/p25-cell01-canonical-attempt001')

    def test_v2_manifest_retains_missing_success_and_exact_original_input(self):
        manifest = json.loads((HERE / 'RUNNER_MANIFEST_V2.json').read_text())
        self.assertEqual(manifest['runner_path'], NS['RUNNER_PATH'])
        self.assertEqual(manifest['runner_sha256'], hashlib.sha256(DRIVER.read_bytes()).hexdigest())
        self.assertEqual(manifest['previous_commit'], NS['CELL00_PUBLICATION'])
        self.assertIsNone(manifest['cell00_prerequisite']['result_sha256'])
        self.assertIs(manifest['cell00_prerequisite']['artifacts_reviewed'], False)
        self.assertEqual(manifest['private_dependencies'], BASE['MANIFEST']['private_dependencies'])
        self.assertEqual(manifest['source_scope'], BASE['MANIFEST']['source_scope'])
        self.assertEqual(manifest['cell00_continuation_provenance']['expected_fresh_owner_order'], ACTUAL005['module_order'][1:])
        self.assertIs(manifest['cell00_continuation_provenance']['previous_aggregate_accepted'], False)
        with self.assertRaisesRegex(RuntimeError, 'DORMANT'):
            NS['ready_manifest'](manifest)


if __name__ == '__main__':
    unittest.main()
