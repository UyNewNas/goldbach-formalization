#!/usr/bin/env python3
"""Offline scope and dormant-gate checks. No compiler or cloud process runs."""
import ast
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import runpy
import sys
import tarfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
DRIVER = Path(sys.argv.pop(1)) if len(sys.argv) > 1 and sys.argv[1].endswith('.py') else Path(__file__).with_name('run_canonical_cell01.py')
NS = runpy.run_path(str(DRIVER))
PACKAGE = ROOT / 'docs/source-only/20261125-p2-5-canonical-char-loader'
SOURCE_MANIFEST = json.loads((PACKAGE / 'MANIFEST.json').read_text())
PUBLISHED = {row['path']: (ROOT / row['path']).read_bytes() for row in SOURCE_MANIFEST['modules'].values()}
input_spec = SOURCE_MANIFEST['existing_canonical_dependency']
PUBLISHED[input_spec['production_path']] = (ROOT / input_spec['production_path']).read_bytes()
LOADER = 'ImbalancedChen.P2Saving16CanonicalCharLoader'
BINDING = 'ImbalancedChen.P2Saving16CanonicalCell01Binding'
INPUT = 'ImbalancedChen.P2OriginalSaving16OriginalInput'
MANIFEST = json.loads(Path(__file__).with_name('RUNNER_MANIFEST.json').read_text())


def canonical_evidence():
    path = ROOT / 'docs/verification/20261126-p2-5-continuation/canonical_evidence.tar.gz'
    prefix = 'canonical/.lake/diagnostic/p25-cell00-canonical-attempt001/'
    with tarfile.open(path) as archive:
        outer_bytes = archive.extractfile(prefix + 'RESULT.json').read()
        owner_bytes = archive.extractfile(prefix + 'canonical/RESULT.json').read()
    assert hashlib.sha256(outer_bytes).hexdigest() == 'edec731af08194ad0b3f57b291491fd1bae67fa9876a84bb1e3bf8b58be5db72'
    assert hashlib.sha256(owner_bytes).hexdigest() == '02da5203b80e6d5a735596ef2f6c1f2f26682304627a8e95f890c0ce2ca1d23b'
    return json.loads(owner_bytes), json.loads(outer_bytes)


class CanonicalCell01Preparation(unittest.TestCase):
    def function(self, name):
        self.assertIn(name, NS, 'Missing Cell01 continuation interface: ' + name)
        return NS[name]

    def test_exact_existing_two_source_graphs(self):
        graphs = self.function('source_graphs')(SOURCE_MANIFEST, PUBLISHED)
        self.assertEqual(set(graphs), {LOADER, BINDING})
        self.assertEqual(set(graphs[LOADER]), {INPUT, LOADER})
        self.assertEqual(set(graphs[BINDING]), {INPUT, LOADER, BINDING})
        self.assertEqual(graphs[BINDING][INPUT]['sha256'], input_spec['sha256'])
        self.assertEqual(graphs[BINDING][LOADER]['sha256'], 'a61bf5fe0b370019f7b3115684dae4ba98ca947604adbd03d01d543528b134a1')
        self.assertEqual(graphs[BINDING][BINDING]['sha256'], 'a18d3ae821babe0d06642aaece7abd73b368bf6196095810f669a5756d40f802')

    def test_changed_source_bytes_rejected(self):
        published = dict(PUBLISHED)
        path = SOURCE_MANIFEST['modules'][BINDING]['path']
        published[path] += b'\n'
        with self.assertRaisesRegex(RuntimeError, 'source|Source'):
            self.function('source_graphs')(SOURCE_MANIFEST, published)

    def test_changed_import_graph_rejected(self):
        manifest = copy.deepcopy(SOURCE_MANIFEST)
        manifest['modules'][BINDING]['imports'].append('ImbalancedChen.P2Saving16CanonicalCell00Binding')
        with self.assertRaisesRegex(RuntimeError, 'import|closure|source'):
            self.function('source_graphs')(manifest, PUBLISHED)

    def test_another_cell_source_rejected(self):
        manifest = copy.deepcopy(SOURCE_MANIFEST)
        manifest['modules']['ImbalancedChen.Cell02'] = manifest['modules'][BINDING]
        with self.assertRaisesRegex(RuntimeError, 'two|scope|module'):
            self.function('source_graphs')(manifest, PUBLISHED)

    def test_wrong_canonical_index_rejected(self):
        manifest = copy.deepcopy(SOURCE_MANIFEST)
        manifest['cell01']['canonical_index'] = 2
        with self.assertRaisesRegex(RuntimeError, 'index|Cell01|cell01'):
            self.function('source_graphs')(manifest, PUBLISHED)

    def assert_dormant_before_root_access(self, missing):
        self.function('require_workflow_ready')
        main = NS['main']
        env = main.__globals__
        keys = ['CELL00_RESULT_SHA256', 'CELL00_PUBLICATION', 'CELL00_ARTIFACTS_REVIEWED', 'ROOT']
        saved = {key: env[key] for key in keys}
        class ForbiddenRoot:
            def __getattr__(self, name):
                raise AssertionError('Filesystem reached before dormant guard: ' + name)
        env.update(CELL00_RESULT_SHA256='0' * 64, CELL00_PUBLICATION='0' * 40,
                   CELL00_ARTIFACTS_REVIEWED=True, ROOT=ForbiddenRoot())
        env[missing] = False if missing == 'CELL00_ARTIFACTS_REVIEWED' else None
        argv = sys.argv
        sys.argv = [str(DRIVER), '0' * 40]
        try:
            with self.assertRaisesRegex(RuntimeError, 'DORMANT'):
                main()
        finally:
            env.update(saved)
            sys.argv = argv

    def test_missing_cell00_result_blocks_before_mutation(self):
        self.assert_dormant_before_root_access('CELL00_RESULT_SHA256')

    def test_missing_cell00_publication_blocks_before_mutation(self):
        self.assert_dormant_before_root_access('CELL00_PUBLICATION')

    def test_missing_cell00_artifact_review_blocks_before_mutation(self):
        self.assert_dormant_before_root_access('CELL00_ARTIFACTS_REVIEWED')

    def test_no_original_input_or_cell00_compilation_target(self):
        self.assertEqual(NS.get('FRESH_MODULES'), [LOADER, BINDING])
        self.assertEqual(NS.get('REQUIRED_PUBLIC_NAMES'), {LOADER: [], BINDING: [BINDING + '.chars01', BINDING + '.ofList_chars01_eq_originalText1']})
        self.assertEqual(NS.get('TIMEOUT_SECONDS'), 180)
        self.assertEqual(NS.get('STRICT_FLAGS'), ['-t0', '-j1', '-M11264', '-DwarningAsError=true', '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000'])

    def test_original_helpers_are_retained(self):
        old_path = ROOT / 'docs/source-only/20261125-p2-5-cell00-canonical/run_canonical_cell00.py'
        self.assertEqual(hashlib.sha256(old_path.read_bytes()).hexdigest(), '7fb5a087044cf2689d6e171b2012b4ff11e46d6e7c37ae6bd8dd12045524e848')
        old = {n.name:n for n in ast.parse(old_path.read_text()).body if isinstance(n, ast.FunctionDef)}
        new = {n.name:n for n in ast.parse(DRIVER.read_text()).body if isinstance(n, ast.FunctionDef)}
        for name in ['require', 'digest', 'sha', 'saved', 'output', 'import_exact', 'publication_bytes', 'copy_exact']:
            self.assertEqual(ast.dump(old[name]), ast.dump(new[name]), name)

    def test_original_input_actual_complete_owned_and_fourteen_file_binding(self):
        prefix = ROOT / 'docs/source-only/20261125-p2-5-decoder/p3-actual'
        receipt_path = prefix / 'p2-private/audit/ImbalancedChen.P2OriginalSaving16OriginalInput/latest.json'
        receipt = json.loads(receipt_path.read_text())
        self.assertEqual(hashlib.sha256(receipt_path.read_bytes()).hexdigest(), NS['INPUT_RECEIPT_SHA256'])
        outer_path = prefix / 'p25-unguarded-sources/attempt001/RUN_RESULT.json'
        outer = json.loads(outer_path.read_text())
        self.assertEqual(hashlib.sha256(outer_path.read_bytes()).hexdigest(), NS['OUTER_INPUT_RECEIPT_SHA256'])
        self.assertEqual(outer['publication_commit'], NS['ORIGINAL_INPUT_PUBLICATION'])
        self.assertIs(outer['accepted'], True)
        self.assertIs(outer['original_input_fresh_data_to_object_bound'], True)
        self.assertEqual(outer['owned_receipts'][INPUT]['receipt'], receipt)
        self.assertEqual(outer['compiled_objects'][INPUT]['sha256'], NS['INPUT_OBJECT_SHA256'])
        self.assertEqual(outer['compiled_objects'][INPUT]['bytes'], 93650960)
        self.assertEqual(outer['compile_records'][INPUT]['closure_signature'], NS['INPUT_CLOSURE_SIGNATURE'])
        self.assertEqual(len(outer['final_input_snapshot']['files']), 14)
        self.assertEqual(sum(row['bytes'] for row in outer['final_input_snapshot']['files']), 93508187)
        source = ROOT / 'verification/part2/run_winner9_private_audit.py'
        self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), MANIFEST['gate_sources']['verification/part2/run_winner9_private_audit.py'])
        node = next(node for node in ast.parse(source.read_text()).body if isinstance(node, ast.FunctionDef) and node.name == 'parse_audit')
        env = {'Path': Path, 'Counter': Counter, 'json': json, 'require': NS['require'],
               'AXIOMS': {'propext', 'Classical.choice', 'Quot.sound'}}
        exec(compile(ast.Module(body=[node], type_ignores=[]), str(source), 'exec'), env)
        folder = receipt_path.parent / 'attempt-001'
        parsed = env['parse_audit'](folder / 'audit.log', INPUT, {INPUT})
        self.assertEqual(parsed['declaration_count'], 3)
        self.assertEqual(parsed, json.loads((folder / 'declarations.json').read_text()))

    def test_original_canonical_stage_remains_separate_from_failed_aggregate(self):
        owner, outer = canonical_evidence()
        self.assertIs(owner['accepted'], True)
        self.assertIs(outer['accepted'], False)
        self.assertEqual(outer['status'], 'CANONICAL_ACCEPTED_CHARPARSE_NOT_ACCEPTED')
        self.assertIs(outer['single_cell_parse_decode_accepted'], False)
        self.assertEqual(owner['fresh_target_object_sha256'], NS['CANONICAL00_OBJECT_SHA256'])
        self.assertEqual(outer['canonical_accepted_object']['receipt_sha256'], NS['CANONICAL00_RECEIPT_SHA256'])

    def test_actual_failed_cell00_does_not_satisfy_workflow(self):
        failed = json.loads((ROOT / 'docs/verification/20261126-p2-5-resumed/consumer-attempt004/RESULT.json').read_text())
        owner, outer = canonical_evidence()
        with self.assertRaisesRegex(RuntimeError, 'Cell00'):
            self.function('validate_workflow_receipts')(failed, owner, outer)

    def test_normal_replay_audit_command_construction_is_unchanged(self):
        old_path = ROOT / 'docs/source-only/20261125-p2-5-cell00-canonical/run_canonical_cell00.py'
        def command_assignment(path):
            stage = next(node for node in ast.parse(path.read_text()).body
                         if isinstance(node, ast.FunctionDef) and node.name == 'run_stage')
            return next(node for node in ast.walk(stage) if isinstance(node, ast.Assign) and
                        any(isinstance(target, ast.Name) and target.id == 'commands' for target in node.targets))
        self.assertEqual(ast.dump(command_assignment(old_path)), ast.dump(command_assignment(DRIVER)))

    def test_live_space_guard_is_immediately_before_each_new_gate(self):
        stage = next(node for node in ast.parse(DRIVER.read_text()).body
                     if isinstance(node, ast.FunctionDef) and node.name == 'run_stage')
        phase = next(node for node in ast.walk(stage) if isinstance(node, ast.For) and
                     isinstance(node.iter, ast.Name) and node.iter.id == 'commands')
        index = next(index for index, node in enumerate(phase.body) if isinstance(node, ast.Assign) and
                     isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and
                     node.value.func.attr == 'run_bounded')
        guard = phase.body[index - 2]
        calls = [node for node in ast.walk(guard) if isinstance(node, ast.Call) and
                 isinstance(node.func, ast.Name) and node.func.id == 'check_disk_space']
        self.assertEqual(len(calls), 1)

    def test_source_manifest_and_execution_readiness_remain_separate(self):
        self.assertEqual(hashlib.sha256((PACKAGE / 'MANIFEST.json').read_bytes()).hexdigest(), NS['SOURCE_MANIFEST_SHA256'])
        self.assertEqual(MANIFEST['fresh_modules'], [LOADER, BINDING])
        self.assertEqual(set(MANIFEST['private_dependencies']), {INPUT})
        self.assertEqual(MANIFEST['private_dependencies'][INPUT]['object_sha256'], NS['INPUT_OBJECT_SHA256'])
        self.assertIsNone(NS['CELL00_RESULT_SHA256'])
        self.assertIs(NS['CELL00_ARTIFACTS_REVIEWED'], False)
        with self.assertRaisesRegex(RuntimeError, 'DORMANT'):
            NS['ready_manifest'](MANIFEST)


if __name__ == '__main__':
    unittest.main()
