"""Only successor admission/scope boundaries; no Lean, cloud or old-suite runs."""
from pathlib import Path
import ast
import copy
import json
import os
import sys
import types
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
RUNNER = HERE.parent / 'run_cell00_three_consumers_v9.py'
BASELINE = HERE.parent / 'run_cell00_four_consumers_v8.py'


def load():
    source = RUNNER if RUNNER.is_file() else BASELINE
    module = types.ModuleType('p25_v9_boundary_under_test')
    module.__file__ = str(source)
    exec(compile(source.read_bytes(), str(source), 'exec'), module.__dict__)
    return module


class ThreeConsumerBoundaries(unittest.TestCase):
    def setUp(self):
        self.driver = load()

    def need(self, name):
        function = getattr(self.driver, name, None)
        self.assertTrue(callable(function), 'Missing successor boundary: ' + name)
        return function

    def test_unbound_prior_evidence_rejects_before_workspace_access(self):
        check = self.need('require_v9_pins')
        self.driver.V8_ARTIFACTS_REVIEWED = False
        self.driver.PRIOR_V8_RESULT_SHA = None
        with self.assertRaisesRegex(RuntimeError, 'SOURCE_ONLY'):
            check()

    def test_only_the_three_unaccepted_consumers_can_execute_gates(self):
        check = self.need('require_new_gate')
        for module in self.driver.FRESH_MODULES[2:]:
            for stage in ['normal', 'replay', 'audit']:
                check(module, stage)
        for module in [self.driver.PARSE_TARGET, self.driver.DECODED,
                       'ImbalancedChen.P2OriginalSaving16OriginalInput']:
            for stage in ['normal', 'replay', 'audit']:
                with self.assertRaisesRegex(RuntimeError, 'Only the three'):
                    check(module, stage)
        with self.assertRaisesRegex(RuntimeError, 'Only the three'):
            check(self.driver.FRESH_MODULES[2], 'normal-rematerialization')

    def test_exact_42_dependency_set_rejects_missing_or_changed_bytes(self):
        check = self.need('validate_dependency_identities')
        root = HERE.parents[3]
        cfg = json.loads((root / 'docs/source-only/20261126-p2-5-cache-rematerialization/RECOVERY_SELECTION.json').read_text())
        identities = {name: row['sha256'] for name, row in cfg['objects'].items()}
        parse_sha = '5bb7d93c7f336040afae0aedfb5b5f26c5c78f9a61400738ca2f299c0760c03f'
        identities[self.driver.PARSE_TARGET] = parse_sha
        check(identities, cfg['objects'], parse_sha)
        missing = dict(identities)
        missing.pop(self.driver.PARSE_TARGET)
        with self.assertRaisesRegex(RuntimeError, '42 exact'):
            check(missing, cfg['objects'], parse_sha)
        changed = dict(identities)
        changed[self.driver.PARSE_TARGET] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, '42 exact'):
            check(changed, cfg['objects'], parse_sha)
        extra = dict(identities)
        extra[self.driver.FRESH_MODULES[2]] = '1' * 64
        with self.assertRaisesRegex(RuntimeError, '42 exact'):
            check(extra, cfg['objects'], parse_sha)

    def test_no_rematerialization_executor_or_second_compiler_entry(self):
        self.assertFalse(hasattr(self.driver, 'execute_rematerialization'))
        tree = ast.parse(RUNNER.read_text())
        parents = {}
        for parent in ast.walk(tree):
            for child in ast.iter_child_nodes(parent):
                parents[child] = parent
        starts = [node for node in ast.walk(tree) if isinstance(node, ast.Call) and
                  isinstance(node.func, ast.Attribute) and node.func.attr == 'Popen']
        self.assertEqual(len(starts), 1)
        node = starts[0]
        while not isinstance(node, ast.FunctionDef):
            node = parents[node]
        self.assertEqual(node.name, 'run_stage')
        self.assertIsInstance(node.body[0], ast.Expr)
        self.assertEqual(node.body[0].value.func.id, 'require_new_gate')

    def test_floor_override_keeps_every_other_source_and_public_interface(self):
        check = self.need('select_floors_sources')
        root = HERE.parents[3]
        old = json.loads((root / self.driver.SELECTION_REL).read_text())
        field = json.loads((root / self.driver.FIELD_SELECTION_REL).read_text())
        earlier = json.loads((root / self.driver.PREVIOUS_SOURCE_OVERRIDE_REL).read_text())
        symbolic = json.loads((root / self.driver.SOURCE_OVERRIDE_REL).read_text())
        parse = json.loads((root / self.driver.PARSE_OVERRIDE_REL).read_text())
        floors = json.loads((root / self.driver.FLOORS_OVERRIDE_REL).read_text())
        before = self.driver.select_parse_sources(
            self.driver.select_symbolic_sources(old, field, earlier, symbolic), parse)
        result = check(before, floors)
        module = self.driver.ORIGINAL_FLOORS
        self.assertEqual(len(result), 45)
        self.assertEqual({k: v for k, v in before.items() if k != module},
                         {k: v for k, v in result.items() if k != module})
        for key in ['project_imports', 'public_namespace', 'public_names']:
            self.assertEqual(result[module][key], before[module][key])
        for key, value in [('public_names', []), ('project_imports', []), ('public_namespace', 'Changed')]:
            wrong = copy.deepcopy(floors)
            wrong['source_spec'][key] = value
            with self.assertRaisesRegex(RuntimeError, 'Floors override changed'):
                check(before, wrong)


class ActualV8EvidenceBoundaries(unittest.TestCase):
    """Use the unchanged actual export, not synthetic owner/receipt fixtures."""
    @classmethod
    def setUpClass(cls):
        cls.driver = load()
        cls.root = HERE.parents[3]
        cls.export = Path(os.environ.get('P25_V8_EVIDENCE_ROOT',
            '/workspace/library-files/p25-recovery-transport/v8-evidence'))
        cls.mapping = json.loads((cls.export / 'FILES_MANIFEST.json').read_text())
        cls.prior = json.loads(cls.local(cls.driver.PRIOR_V8_OUT / 'RESULT.json').read_text())
        cls.remat = json.loads(cls.local(cls.driver.PRIOR_V8_OUT / 'rematerialization/RESULT.json').read_text())
        cls.cfg = json.loads((cls.root / 'docs/source-only/20261126-p2-5-cache-rematerialization/RECOVERY_SELECTION.json').read_text())
        cls.selection = json.loads((cls.root / cls.driver.FRESH_SELECTION_REL).read_text())

    @classmethod
    def local(cls, name):
        return Path(cls.mapping[str(name)]['path'])

    def test_actual_failed_aggregate_and_completed_historical_normals_are_compatible(self):
        self.driver.validate_v8_terminal_metadata(self.prior, self.remat, self.cfg, self.selection)

    def test_actual_metadata_rejects_relabelling_or_forged_normal_records(self):
        d = self.driver
        mutations = [
            ('aggregate accepted', lambda p, r: p.update(accepted=True)),
            ('Parse unaccepted', lambda p, r: p['modules'][d.PARSE_TARGET].update(accepted=False)),
            ('Parse missing owned', lambda p, r: p['modules'][d.PARSE_TARGET].update(owned_count=6)),
            ('Floors no timeout', lambda p, r: p['modules'][d.ORIGINAL_FLOORS]['stages']['normal'].update(timed_out=False)),
            ('pending owner started', lambda p, r: p['modules'][d.CONTINUATION_MODULES[-1]]['stages'].update(normal={})),
            ('invented root after', lambda p, r: p.update(fresh_context_after=p['fresh_context_before'])),
            ('invented recovery credit', lambda p, r: r.update(accepted=True)),
            ('Parse unsafe helper', lambda p, r: next(v for v in p['modules'][d.PARSE_TARGET]['owned_declarations']
                if v['name'].endswith('.' + d.PARSE_PRIVATE_HELPERS[0])).update(unsafe=True)),
        ]
        for name, mutate in mutations:
            with self.subTest(name=name):
                prior, remat = copy.deepcopy(self.prior), copy.deepcopy(self.remat)
                mutate(prior, remat)
                with self.assertRaises(RuntimeError):
                    d.validate_v8_terminal_metadata(prior, remat, self.cfg, self.selection)
        for name, mutate in [
                ('wrong normal object', lambda row: row['object'].update(sha256='0' * 64)),
                ('non-strict normal', lambda row: row['command'].remove('-DwarningAsError=true')),
                ('changed witness', lambda row: row['input_snapshot_after'][0].update(sha256='0' * 64))]:
            with self.subTest(name=name):
                prior, remat = copy.deepcopy(self.prior), copy.deepcopy(self.remat)
                mutate(remat['normal_stages'][0])
                prior['normal_rematerialization_stages'] = copy.deepcopy(remat['normal_stages'])
                with self.assertRaisesRegex(RuntimeError, 'historical normal command/object/witness'):
                    d.validate_v8_terminal_metadata(prior, remat, self.cfg, self.selection)

    def test_actual_three_contexts_preserve_identity_without_synthesized_annotations(self):
        d = self.driver
        descriptors = [self.prior['fresh_context_before'], self.remat['fresh_context_after'],
                       self.prior['complete_external_before']]
        snapshots = [json.loads(self.local(row['path']).read_text()) for row in descriptors]
        for descriptor, snapshot in zip(descriptors, snapshots):
            self.assertEqual({k: self.mapping[descriptor['path']][k] for k in ['bytes', 'sha256']},
                             {k: descriptor[k] for k in ['bytes', 'sha256']})
            self.assertEqual(snapshot['provider_roots'], self.selection['external_provider_roots'])
            self.assertEqual(snapshot['entries'], snapshots[0]['entries'])
            self.assertEqual(len(snapshot['entries']), 5312)
            self.assertEqual(sum(len(row['companions']) for row in snapshot['entries']), 10624)
            self.assertFalse(snapshot['historical_missing_hashes_invented'])
        self.assertNotIn(str(d.PRIOR_V8_OUT / 'FRESH_CONTEXT_AFTER.json'), self.mapping)
        self.assertEqual(len(self.mapping), 40)

    def test_parse_complete_audit_is_the_exact_seven_record_export(self):
        d = self.driver
        d.SOURCES = d.select_floors_sources(self.prior['source_graph'],
            json.loads((self.root / d.FLOORS_OVERRIDE_REL).read_text()))
        d.SOURCES = d.select_pending_source_overlays(d.SOURCES,
            json.loads((self.root / d.PENDING_SOURCE_REVIEW_REL).read_text()), self.prior['source_graph'])
        owner = self.prior['modules'][d.PARSE_TARGET]
        records, inventory, imports = d.read_audit(self.local(owner['stages']['audit']['log']), d.PARSE_TARGET)
        self.assertEqual(records, owner['owned_declarations'])
        self.assertEqual(records, json.loads(self.local(owner['declarations']['path']).read_text()))
        self.assertEqual(inventory, json.loads(self.local(owner['inventory']['path']).read_text()))
        self.assertEqual(imports, owner['actual_project_closure'])
        self.assertEqual(len(records), 7)
        self.assertEqual(d.validate_parse_helpers(records), owner['private_expression_helpers'])
        self.assertEqual(owner['private_expression_helpers'], self.prior['private_parse_helper_records'])
        template = (self.root / Path(self.prior['audit_template']['path']).relative_to(d.ROOT)).read_text()
        self.assertEqual(self.local(owner['audit_source']['path']).read_text(), template.replace(d.PAYLOAD, d.PARSE_TARGET))

    def test_root_selected_pending_overlays_change_only_the_three_unaccepted_sources(self):
        d = self.driver
        select = getattr(d, 'select_pending_source_overlays', None)
        self.assertTrue(callable(select), 'Missing exact root-selected pending-source overlay boundary')
        review = json.loads((self.root / 'docs/source-only/20261126-p2-5-cell00-floors-transport/optional-pending-consumers/ROOT_SELECTED_SOURCE_REVIEW.json').read_text())
        original = self.prior['source_graph']
        floors = d.select_floors_sources(original, json.loads((self.root / d.FLOORS_OVERRIDE_REL).read_text()))
        selected = select(floors, review, original)
        self.assertEqual({m for m in selected if selected[m] != original[m]}, set(d.CONTINUATION_MODULES))
        self.assertEqual(len([m for m in selected if selected[m] == original[m]]), 42)
        for module in selected:
            for key in ['project_imports', 'public_namespace', 'public_names']:
                self.assertEqual(selected[module].get(key), original[module].get(key))
        for label, mutate in [
                ('accepted owner target', lambda x: x['rows'][0].update(module=d.PARSE_TARGET)),
                ('extra override', lambda x: x['rows'].append(copy.deepcopy(x['rows'][0]))),
                ('changed imports', lambda x: x['rows'][0]['source_spec'].update(project_imports=[])),
                ('changed public names', lambda x: x['rows'][1]['source_spec'].update(public_names=[])),
                ('wrong source SHA', lambda x: x['rows'][0]['new_source'].update(sha256='0' * 64)),
                ('invented previous failure', lambda x: x['rows'][1].update(prior_actual_status='NORMAL_FAILED'))]:
            with self.subTest(label=label):
                bad = copy.deepcopy(review)
                mutate(bad)
                with self.assertRaises(RuntimeError):
                    select(floors, bad, original)
        wrong_protected = copy.deepcopy(floors)
        wrong_protected[d.PARSE_TARGET]['source_sha256'] = '0' * 64
        with self.assertRaises(RuntimeError):
            select(wrong_protected, review, original)


if __name__ == '__main__':
    unittest.main(verbosity=2)
