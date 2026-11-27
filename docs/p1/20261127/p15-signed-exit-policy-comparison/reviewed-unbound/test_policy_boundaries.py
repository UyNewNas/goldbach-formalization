"""Local adapter gates using actual raw probe receipts; no Lean/Git/cloud calls."""
import copy
import hashlib
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
NEXT = HERE.parent
SOURCE_SHA = 'c60992855b519d9767e66f31c9007dd18f2292e326e28539fc2a39d1d831b57f'
RAW = NEXT / 'exact-probe-evidence/policy' / SOURCE_SHA / 'attempt-00000'
PARENT_RAW = NEXT.parent.parent / 'p15-next-medium-formal/exact-acceptance-evidence'
# The parent evidence is a workspace sibling of p15-next-medium.
PARENT_RAW = NEXT.parents[1] / 'p15-next-medium-formal/exact-acceptance-evidence'


def read(name):
    return json.loads((RAW / name).read_bytes())


def namespace():
    path = HERE / 'run_policy.py'
    scope = {'__name__': 'local_policy_adapter_gate_test', '__file__': str(path)}
    exec(compile(path.read_bytes(), str(path), 'exec'), scope)
    return scope


class PolicyBoundaries(unittest.TestCase):
    def setUp(self):
        self.n = namespace()
        self.target = self.n['TARGET']
        self.readonly = json.loads((PARENT_RAW / 'partition-readonly/READONLY_RESULT.json').read_bytes())
        self.parent_binding = json.loads((NEXT / 'PARTITION_BINDING.json').read_bytes())

    def test_unbound_precedes_operative_helpers(self):
        events = []
        def forbidden(*args, **kwargs):
            events.append('unexpected operative call')
            raise AssertionError(events[-1])
        actual_load = self.n['load']
        for name in ('git', 'regular', 'load', 'worker', 'dispatch', 'check'):
            self.n[name] = forbidden
        with self.assertRaisesRegex(ValueError, 'UNBOUND'):
            self.n['main']()
        with self.assertRaisesRegex(ValueError, 'UNBOUND'):
            actual_load('1' * 40)
        self.assertEqual(events, [])

    def test_entire_original_source_is_immutable(self):
        source = (RAW / self.n['NAME']).read_bytes()
        self.n['verify_source'](source)
        self.assertEqual(source, (NEXT.parent / 'reference' / self.n['NAME']).read_bytes())
        with self.assertRaisesRegex(ValueError, 'any change'):
            self.n['verify_source'](source + b'\n')

    def test_complete_actual_input_inventory(self):
        files = {}
        exported = json.loads((NEXT / 'EXACT_PROBE_FILES.json').read_bytes())
        for row in exported:
            data = Path(row['local']).read_bytes()
            self.assertEqual(len(data), row['bytes'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'])
            rel = str(Path(row['local']).relative_to(RAW))
            files[rel] = {'bytes': len(data), 'sha256': row['sha256']}
        self.assertEqual(set(files), set(self.n['PROBE_FILES']))
        self.n['INPUTS'] = {'probe': {'job_id': self.n['PROBE_JOB'],
                                     'directory': str(self.n['PROBE_RUN']), 'files': files}}
        self.n['validate_inputs']()
        del files['serialized-probe-command.json']
        with self.assertRaisesRegex(ValueError, 'incomplete original probe'):
            self.n['validate_inputs']()

    def test_actual_probe_requires_same_source_parent_and_zero_credit(self):
        result = read('PROBE_RESULT.json')
        verify = self.n['verify_probe_scope']
        verify(result, self.readonly, self.parent_binding)
        for key, value in [('probe_passed', False), ('new_owner_accepted', True),
                           ('project_dependency_count', 40), ('output_object_requested', True)]:
            bad = copy.deepcopy(result)
            bad[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                verify(bad, self.readonly, self.parent_binding)
        other_parent = copy.deepcopy(self.readonly)
        other_parent['identity']['commit'] = '0' * 40
        with self.assertRaises(ValueError):
            verify(result, other_parent, self.parent_binding)

    def test_inner_outer_commands_and_finished_lane_are_all_required(self):
        state = '/workspace/blue-build-tools/member-runtime-evidence/state.json'
        guard = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', state]
        run = self.n['PROBE_RUN']
        worker = ['python3', '-B', str(run / 'probe_driver.py'), '--worker']
        outer = ['python3', '/workspace/blue-build-tools/serialize_validation_lane.py',
                 '--state', state, '--receipt', str(run / 'LANE.json')] + worker
        cases = [
            ('probe', guard + ['lake', '--no-build', 'env', 'lean', str(run / self.n['NAME'])]),
            (self.target + '/direct-import-stock-readiness',
             guard + ['lake', '--no-build', 'build', '+' + self.n['PARTITION'] + ':olean']),
            ('serialized-probe', outer),
        ]
        for name, argv in cases:
            record, log = read(name + '-command.json'), (RAW / (name + '.log')).read_bytes()
            self.n['command_record'](record, log, argv, run / (name + '.log'))
            bad = copy.deepcopy(record)
            bad['exit_code'] = 1
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.n['command_record'](bad, log, argv, run / (name + '.log'))
        bad = read('probe-command.json')
        bad['actual_built_modules'] = [self.n['PARTITION']]
        with self.assertRaises(ValueError):
            self.n['command_record'](bad, (RAW / 'probe.log').read_bytes(), cases[0][1], run / 'probe.log')
        lane = read('LANE.json')
        expected_state_sha = read('PRESERVED_BEFORE.json')['original_inputs']['existing_owners']['environment']['runtime'][state]['sha256']
        self.n['verify_finished_lane'](lane, worker, state, expected_state_sha)
        lane['status'] = 'VALIDATION_LANE_RUNNING'
        with self.assertRaises(ValueError):
            self.n['verify_finished_lane'](lane, worker, state, expected_state_sha)


if __name__ == '__main__':
    unittest.main(verbosity=2)
