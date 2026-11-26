#!/usr/bin/env python3
"""Local new-wrapper boundary tests; no cloud, Git, Lean, or old proof suite.

All successful new-owner/install run fixtures below are synthetic control-flow
fixtures, not actual acceptance evidence. No new owned/public count is guessed.
"""
from pathlib import Path
from types import ModuleType, SimpleNamespace as NS
from unittest.mock import patch
from contextlib import ExitStack, redirect_stdout
import ast
import copy
import hashlib
import io
import json
import tempfile
import unittest

HERE = Path(__file__).parent
BASE = Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')


def module(path, name):
    value = ModuleType(name); value.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), value.__dict__)
    return value


r = module(HERE / 'run_trimlog.py', 'trimlog_boundary_test')
i = module(HERE / 'install_trimlog_source.py', 'trimlog_installer_boundary_test')
SOURCE = Path('/tmp/p15-exact-medium-correction/P1OriginalSingletonAtlasTrimLogAccuracy.lean').read_bytes()
MANIFEST = json.loads(Path('/tmp/p15-entrypoint-ag/SOURCE_MANIFEST.json').read_bytes())
GRAPH = {m: row['imports'] for m, row in MANIFEST['project_sources'].items()}
COMMIT = 'a' * 40  # Synthetic local identity, never used for Git or a real receipt.


def closure(graph, modules):
    result = set()
    def visit(m):
        if m not in result:
            result.add(m)
            for dep in graph[m]:
                visit(dep)
    for m in modules:
        visit(m)
    return result


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def full_artifacts(module):
    return {module + ':slot:%02d' % n: None for n in range(21)}


class Boundaries(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='trimlog-new-boundary-')
        self.root = Path(self.temporary.name)
        self.addCleanup(self.temporary.cleanup)
        self.patches = ExitStack(); self.addCleanup(self.patches.close)

    def replace(self, obj, **values):
        for key, value in values.items():
            self.patches.enter_context(patch.object(obj, key, value))

    def test_01_reviewed_functions_and_actual_origin_are_unchanged(self):
        baseline = (HERE / 'run_trimlog.review-baseline.py').read_bytes()
        self.assertEqual(r.raw_fp(baseline), {'bytes': 27648,
            'sha256': '05bbff77f06ef0b5387bd24511ae94aff2808999c41b24b0f62e0b8936307340'})
        def functions(raw):
            text = raw.decode(); tree = ast.parse(text)
            return {node.name: ast.get_source_segment(text, node) for node in tree.body if isinstance(node, ast.FunctionDef)}
        old, new = functions(baseline), functions((HERE / 'run_trimlog.py').read_bytes())
        self.assertEqual({name for name in old if old[name] != new[name]},
            {'owner_history', 'new_spec', 'check', 'main'})
        self.assertEqual(set(new) - set(old), {'read_command', 'read_installation', 'read_completed_run'})
        self.assertEqual(r.raw_fp(SOURCE), r.SOURCE_FP)
        self.assertEqual([line for line in SOURCE.decode().splitlines() if line.startswith('import ')],
            ['import ImbalancedChen.P1OriginalSingletonAtlasTrim'])
        for name, value in [('ae', r.AE_DRIVER_FP), ('ag', r.AG_DRIVER_FP)]:
            self.assertEqual(r.raw_fp(Path('/tmp/p15-entrypoint-' + name + '/run_selected.py').read_bytes()), value)
        self.assertNotIn(r.TARGET, MANIFEST['targets'])
        self.assertEqual(len(GRAPH), 360)

    def test_02_actual_graph_uses_full_snapshot_and_exact_153_dependencies(self):
        project = self.root / 'project'; source = project / r.SOURCE
        source.parent.mkdir(parents=True); source.write_bytes(SOURCE)
        prefix = closure(GRAPH, r.AE_OWNERS)
        self.assertEqual(len(prefix), 153)
        deps = prefix - set(r.AE_OWNERS)
        full = {m: full_artifacts(m) for m in deps}
        state = NS(ag=NS(graph=GRAPH, sources={m: row['sha256'] for m, row in MANIFEST['project_sources'].items()}, review={}),
            ae=NS(active=prefix, dependency_pins={m: dict(list(v.items())[:2]) for m, v in full.items()},
                baseline={'preserved_dependency_artifacts': full}),
            ae_bindings={m: {'all_observed_target_artifacts': full_artifacts(m)} for m in r.AE_OWNERS}, retained={})
        state.ag.baseline = {'fixture': 'old AG context'}
        expanded = {**GRAPH, r.TARGET: [r.ATLAS]}; active = closure(expanded, [r.TARGET])
        sources = {**state.ag.sources, r.TARGET: r.SOURCE_FP['sha256']}
        observed = lambda project, selected: ({m: expanded[m] for m in active},
            {m: {'sha256': sources[m]} for m in active})
        c = NS(commit=COMMIT, identity={'fixture': 'new owner'},
            ag=NS(h=NS(closure=closure, project_graph=observed)),
            g=NS(snapshot=lambda helper, spec: {'dependencies': copy.deepcopy(spec.dependency_pins)}))
        self.replace(r, PROJECT=project, read_installation=lambda c, state: ({'fixture': 'install verified'}, {}))
        spec = r.new_spec(c, state)
        self.assertEqual((len(spec.graph), len(spec.active), len(spec.dependency_pins)), (361, 154, 153))
        self.assertEqual(set(spec.dependency_pins), prefix)
        self.assertTrue(all(len(v) == 21 for v in spec.dependency_pins.values()))
        self.assertTrue(all(len(v) == 2 for v in state.ae.dependency_pins.values()))
        state.ae.baseline['preserved_dependency_artifacts'].pop(next(iter(deps)))
        with self.assertRaisesRegex(RuntimeError, 'dependency inventory'):
            r.new_spec(c, state)

    def test_03_fresh_identical_partial_and_artifact_gates(self):
        empty = full_artifacts(r.TARGET)
        r.require_new_slot(None, empty, [], installed=False)
        r.require_new_slot(r.SOURCE_FP, empty, [], installed=False)
        r.require_new_slot(r.SOURCE_FP, empty, [], installed=True)
        cases = [(None, empty, [], True), ({'bytes': 1, 'sha256': 'wrong'}, empty, [], False),
            (r.SOURCE_FP, empty, [self.root / 'started-owner'], False),
            (r.SOURCE_FP, {**empty, next(iter(empty)): {'bytes': 1, 'sha256': 'present'}}, [], False),
            (r.SOURCE_FP, {}, [], False)]
        for source, artifacts, history, installed in cases:
            with self.subTest(source=source, history=history, slots=len(artifacts)):
                with self.assertRaises(RuntimeError):
                    r.require_new_slot(source, artifacts, history, installed=installed)
        self.replace(r, ROOT=self.root)
        commit = self.root / COMMIT; commit.mkdir(); outside = self.root / 'outside'; outside.mkdir()
        (commit / r.TARGET).symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'nonregular owner'):
            r.owner_history(COMMIT)

    def test_04_exclusive_creation_durable_identical_and_refusal(self):
        source = self.root / 'project' / 'ImbalancedChen' / 'Draft.lean'; source.parent.mkdir(parents=True)
        self.assertEqual(i.install_exclusive(r, source, SOURCE), 'EXCLUSIVE_NEW_CANONICAL_SOURCE')
        inode = source.stat().st_ino
        self.assertEqual(i.install_exclusive(r, source, SOURCE), 'IDENTICAL_SOURCE_BEFORE_OWNER_START')
        self.assertEqual(source.stat().st_ino, inode)
        source.write_bytes(b'prior partial data')
        with self.assertRaisesRegex(RuntimeError, 'no replacement'):
            i.install_exclusive(r, source, SOURCE)
        self.assertEqual(source.read_bytes(), b'prior partial data')
        link = self.root / 'link'; link.symlink_to(source.parent, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'symlink'):
            i.install_exclusive(r, link / 'Another.lean', SOURCE)
        self.assertFalse((source.parent / 'Another.lean').exists())

    def run_fixture(self):
        project = self.root / 'project'; project.mkdir()
        root = self.root / 'acceptance'; install = self.root / 'install'
        self.replace(r, PROJECT=project, ROOT=root, INSTALL_ROOT=install)
        preservation = {'fixture': 'immutable prior contexts verified separately'}
        self.replace(r, preservation_summary=lambda state: preservation)
        diagnostic = {'actual_built_modules': [], 'actual_failed_modules': [],
            'project_error_count': 0, 'project_error_sections': []}
        helper = NS(guard=lambda lane, argv: ['fixture-guard', str(lane), *argv],
            serialize=lambda lane, lane_path, argv: ['fixture-serialize', str(lane), str(lane_path), *argv])
        c = NS(commit=COMMIT, identity={'fixture': 'independent module identity'}, script=b'fixture adapter bytes',
            ag=NS(api=NS(read_json=lambda path: json.loads(path.read_bytes())), h=helper,
                ops=NS(diagnostics=lambda path: copy.deepcopy(diagnostic))))
        state = NS(git={'fixture': 'unchanged original Git'})
        spec = NS(baseline={'fixture': '154 sources and 153 dependency context already validated'})
        def command(run, name, argv):
            log = run / (name + '.log'); log.parent.mkdir(parents=True, exist_ok=True)
            log.write_bytes(b'Fixture only: no subprocess or compiler was executed.\n')
            binding = r.fp(log)
            record = {'exit_code': 0, 'argv': list(map(str, argv)), 'cwd': str(project),
                'log': str(log), 'log_bytes': binding['bytes'], 'log_sha256': binding['sha256'], **diagnostic}
            save(run / (name + '-command.json'), record)
            return record
        return c, state, spec, preservation, command

    def test_05_installation_receipt_requires_complete_same_commit_chain(self):
        c, state, _, preservation, command = self.run_fixture()
        run = r.INSTALL_ROOT / COMMIT / 'runs/attempt-00000'; run.mkdir(parents=True)
        script = b'fixture installer bytes'
        self.replace(r, git_file=lambda commit, path: script)
        executed = run / 'executed-installer.py'; executed.write_bytes(script)
        for stem, value in [('OLD_CONTEXT', preservation), ('GIT', state.git)]:
            save(run / (stem + '_BEFORE.json'), value); save(run / (stem + '_AFTER.json'), value)
        worker = {'schema': 'p15_independent_trimlog_source_install_v1', 'identity': c.identity,
            'installer': {'path': r.INSTALLER, **r.raw_fp(script)}, 'source_installed': True,
            'source_before': None, 'source_after': r.SOURCE_FP, 'installation_action': 'EXCLUSIVE_NEW_CANONICAL_SOURCE',
            'normal_or_kernel_commands_executed': 0, 'new_owner_accepted': False, 'whole_P1_5_complete': False,
            'preservation': preservation}
        save(run / 'WORKER_RESULT.json', worker)
        result = {**worker, 'worker_exit_code': 0, 'source_install_complete': True}
        save(run / 'SOURCE_INSTALL_RESULT.json', result)
        command(run, 'serialized-trimlog-install', c.ag.h.serialize(0, run / 'TRIMLOG_INSTALL_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', COMMIT, '--install', '--inside-lane', str(run)]))
        binding, pins = r.read_installation(c, state)
        self.assertEqual(binding['run'], str(run)); self.assertEqual(len(pins), 9)
        result['worker_exit_code'] = 3; save(run / 'SOURCE_INSTALL_RESULT.json', result)
        with self.assertRaisesRegex(RuntimeError, 'terminal binding'):
            r.read_installation(c, state)
        result['worker_exit_code'] = 0; save(run / 'SOURCE_INSTALL_RESULT.json', result)
        executed.write_bytes(script + b'changed')
        with self.assertRaisesRegex(RuntimeError, 'script differs'):
            r.read_installation(c, state)

    def test_06_completed_read_requires_successful_run_stock_and_unchanged_log(self):
        c, state, spec, preservation, command = self.run_fixture()
        run = r.ROOT / COMMIT / 'runs/attempt-00000'; run.mkdir(parents=True)
        executed = run / 'executed-trimlog.py'; executed.write_bytes(c.script)
        owner = {'fixture': 'immutable full-owned normal/audit reader returned complete owner'}
        for stem, value in [('CONTEXT', spec.baseline), ('GIT', state.git)]:
            save(run / (stem + '_BEFORE.json'), value); save(run / (stem + '_AFTER.json'), value)
        command(run, 'serialized-trimlog', c.ag.h.serialize(0, run / 'TRIMLOG_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', COMMIT, '--run', '--inside-lane', str(run)]))
        stock = command(run, 'final-stock-readiness', c.ag.h.guard(0, ['lake', '--no-build', 'build', '+' + r.TARGET + ':olean']))
        direct = command(run / r.TARGET, 'direct-import-stock-readiness', c.ag.h.guard(0,
            ['lake', '--no-build', 'build', '+' + r.ATLAS + ':olean']))
        worker = {'schema': 'p15_independent_trimlog_acceptance_v1', 'identity': c.identity,
            'targets': [r.TARGET], 'accepted_owners': [r.TARGET], 'failures': {}, 'owner': owner,
            'preservation': preservation, 'final_stock_readiness': stock, 'direct_import_readiness': direct}
        save(run / 'WORKER_RESULT.json', worker)
        with self.assertRaisesRegex(RuntimeError, 'no unique successful'):
            r.read_completed_run(c, state, spec, owner)
        result = {**worker, 'worker_exit_code': 0, 'new_owner_accepted': True}
        save(run / 'RESULT.json', result)
        self.assertEqual(r.read_completed_run(c, state, spec, owner)['path'], str(run))
        (run / 'final-stock-readiness.log').write_bytes(b'changed')
        with self.assertRaisesRegex(RuntimeError, 'scope/log/diagnostic'):
            r.read_completed_run(c, state, spec, owner)

    def outer_main(self, *, missing_worker=False, changed_git=False, installer=False):
        code = i if installer else r
        root = self.root / ('install-case' if installer else 'formal-case')
        root.mkdir()
        current = {'fixture': 'original Git'}; git_calls = []
        def git_state(repo):
            git_calls.append(None)
            return {'fixture': 'changed Git'} if changed_git and len(git_calls) > 1 else current
        def attempt(parent):
            path = parent / 'attempt-00000'; path.mkdir(parents=True); return path
        def write_frozen(path, payload):
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(payload)
        worker = {'schema': 'p15_independent_trimlog_source_install_v1' if installer else 'p15_independent_trimlog_acceptance_v1',
            'identity': {'fixture': 'identity'}, 'whole_P1_5_complete': False}
        if installer:
            worker.update(source_installed=True, new_owner_accepted=False)
        else:
            worker.update(targets=[r.TARGET], accepted_owners=[r.TARGET], failures={})
        def dispatch(run, name, argv, **kw):
            if not missing_worker:
                save(run / 'WORKER_RESULT.json', worker)
            return {'exit_code': 3 if missing_worker else 0, 'actual_built_modules': [], 'actual_failed_modules': []}
        c = NS(commit=COMMIT, script=b'fixture adapter', installer=b'fixture installer', identity=worker['identity'],
            ag=NS(d=NS(attempt=attempt, original_git_state=git_state, save=save, write_frozen=write_frozen),
                h=NS(serialize=lambda lane, lane_path, argv: argv), ops=NS(run=dispatch),
                api=NS(read_json=lambda path: json.loads(path.read_bytes()))))
        if installer:
            self.replace(i, load=lambda commit, executed: (r, c))
            self.replace(r, INSTALL_ROOT=root)
        else:
            self.replace(r, load=lambda commit, executed: c, ROOT=root)
        self.replace(code.sys, argv=[code.__file__, '--source-commit', COMMIT, '--install' if installer else '--run'])
        with redirect_stdout(io.StringIO()):
            exit_code = code.main()
        path = root / COMMIT / 'runs/attempt-00000' / ('SOURCE_INSTALL_RESULT.json' if installer else 'RESULT.json')
        return exit_code, json.loads(path.read_bytes())

    def test_07_formal_dispatch_and_final_git_failures_cannot_publish_success(self):
        code, result = self.outer_main(changed_git=True)
        self.assertNotEqual(code, 0); self.assertFalse(result['new_owner_accepted']); self.assertIn('git_error', result)
        # A separate local directory is required because evidence is never overwritten.
        self.root = self.root / 'second'; self.root.mkdir()
        code, result = self.outer_main(missing_worker=True)
        self.assertNotEqual(code, 0); self.assertFalse(result['new_owner_accepted']); self.assertIn('dispatch_error', result)
        self.assertEqual(result['accepted_owners'], [])

    def test_08_installer_final_git_failure_and_missing_worker_cannot_complete(self):
        code, result = self.outer_main(changed_git=True, installer=True)
        self.assertNotEqual(code, 0); self.assertFalse(result['source_install_complete']); self.assertIn('git_error', result)
        self.assertFalse(result['new_owner_accepted'])
        self.root = self.root / 'second'; self.root.mkdir()
        code, result = self.outer_main(missing_worker=True, installer=True)
        self.assertNotEqual(code, 0); self.assertFalse(result['source_install_complete']); self.assertIn('dispatch_error', result)
        self.assertFalse(result['new_owner_accepted'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
