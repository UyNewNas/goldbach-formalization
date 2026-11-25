"""Exercise retained-history decisions before the external compiler boundary."""
import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest

spec = importlib.util.spec_from_file_location('selected', Path(__file__).with_name('run_selected.py'))
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class CompilerReached(Exception):
    pass


class RetryHistory(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.old_root = runner.ROOT
        runner.ROOT = self.root
        self.owner = runner.TARGETS[0]
        self.before, self.after = 'a' * 40, 'b' * 40
        self.binding = {'source_commit': self.after, 'project_sources': {self.owner: 'source'},
                        'dependency_objects_and_traces': {'dependency.olean': 'object'},
                        'configuration': {'lean-toolchain': 'toolchain'}, 'existing_runtime': 'runtime'}

        def write_frozen(path, data):
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.exists():
                assert path.read_bytes() == data
            else:
                path.write_bytes(data)

        def normal(*args):
            raise CompilerReached()

        self.helpers = SimpleNamespace(
            d=SimpleNamespace(write_frozen=write_frozen), e9=b'unchanged audit runner', h=None, ops=None,
            api=SimpleNamespace(normal_one=normal, context=lambda *args: self.binding))

    def tearDown(self):
        runner.ROOT = self.old_root
        self.tmp.cleanup()

    def save(self, path, value):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))

    def prior_normal(self, successful=False):
        folder = self.root / self.before / self.owner / 'normal' / self.owner
        binding = dict(self.binding, source_commit=self.before)
        self.save(folder / 'attempt-00000/CONTEXT_BEFORE.json', binding)
        self.save(folder / 'attempt-00000/normal-started.json', {'argv': ['original compiler command']})
        if successful:
            self.save(folder / 'NORMAL_PASS.json', {'dependency_context': binding})
        return folder

    def outcome(self):
        try:
            runner.run_owner(self.helpers, self.after, self.root / self.after,
                             self.root / 'run', self.owner, {}, {})
        except CompilerReached:
            return 'COMPILER_REACHED'
        except ValueError as error:
            return str(error)
        self.fail('expected either a retained-history hold or the compiler boundary')

    def test_docs_only_commit_does_not_repeat_failed_normal(self):
        self.prior_normal()
        self.assertIn('RETAINED_HISTORY_REQUIRES_INSPECTION', self.outcome())

    def test_docs_only_commit_does_not_rebuild_lost_successful_output(self):
        self.prior_normal(successful=True)
        self.assertIn('RETAINED_HISTORY_REQUIRES_INSPECTION', self.outcome())

    def test_prior_partial_audit_is_not_hidden_by_new_commit(self):
        self.prior_normal(successful=True)
        (self.root / self.before / self.owner / 'audits/key/lane-0').mkdir(parents=True)
        self.assertIn('RETAINED_HISTORY_REQUIRES_INSPECTION', self.outcome())

    def test_prepared_plan_without_audit_directory_is_held(self):
        self.save(self.root / self.after / self.owner / 'plans/key.json', {'plan': 'retained'})
        self.assertIn('PARTIAL_AUDIT_REQUIRES_INSPECTION', self.outcome())

    def test_changed_dependency_context_can_reach_compiler(self):
        self.prior_normal()
        self.binding['dependency_objects_and_traces'] = {'dependency.olean': 'repaired-object'}
        self.assertEqual('COMPILER_REACHED', self.outcome())

    def test_same_commit_changed_dependency_can_retry_failed_normal(self):
        self.before = self.after
        self.prior_normal()
        self.binding['dependency_objects_and_traces'] = {'dependency.olean': 'repaired-object'}
        self.assertEqual('COMPILER_REACHED', self.outcome())


if __name__ == '__main__':
    unittest.main()
