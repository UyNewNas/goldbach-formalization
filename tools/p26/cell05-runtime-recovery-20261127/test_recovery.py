#!/usr/bin/env python3
"""Bounded local negative tests; never invoke cloud, Lean, or a historical driver.

The runtime tests execute the unchanged original capture function with a ten-root
temporary byte fixture. Only its input-evidence provider is a test fixture;
no imported historical module is monkeypatched. These are unit tests, not a
claim that live P2 recovery or any historical proof validation has succeeded.
"""
from pathlib import Path
import argparse
import ast
import copy
from contextlib import contextmanager
import hashlib
import importlib
import json
import os
import py_compile
import subprocess
import sys
import tempfile
import types
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).absolute().parent
core = types.ModuleType('test_recovery_core')
core.__file__ = str(HERE / 'protocol_core.py')
exec(compile((HERE / 'protocol_core.py').read_bytes(), core.__file__, 'exec'), core.__dict__)
ORIGINAL = None


def authenticated_functions(filename, names, namespace):
    verifier = (ORIGINAL / 'tools/p26/cell05-remaining9-run-20261126/REMAINING9_VERIFIER.json').read_bytes()
    anchor = json.loads((HERE / 'ANCHORS.json').read_bytes())['remaining9']['verifier']
    core.require(core.same(core.pin(verifier), anchor), 'Original test verifier changed')
    config = json.loads(verifier)
    path = ORIGINAL / 'tools/p26/cell05-remaining9-run-20261126' / filename
    identity = next(r for r in config['workflow_files'] if r['relative_path'] == filename)
    data = core.read_bytes(path)
    core.require(core.same(core.pin(data), identity), 'Original test function source changed')
    tree = ast.parse(data, filename=str(path))
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name in names]
    core.require({node.name for node in functions} == set(names), 'Missing original test function')
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(path), 'exec'), namespace)


class RecoveryBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='recovery-test-', dir=HERE)
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    @contextmanager
    def original_runtime_module(self):
        """Import real frozen runtime/evidence helpers without replacing require."""
        spec = copy.deepcopy(core.read(HERE / 'ANCHORS.json')['remaining9'])
        spec['stage'] = str(ORIGINAL)
        spec['verifier']['path'] = str(ORIGINAL / spec['tool_relative_path'] / spec['verifier_name'])
        _, _, sources, _ = core.authenticate_family(spec)
        finder = core.PinnedSourceFinder(sources)
        sys.meta_path.insert(0, finder)
        try:
            runtime = importlib.import_module('runtime_compat')
            finder.check_loaded()
            yield runtime
            finder.check_loaded()
        finally:
            sys.meta_path.remove(finder)
            for name in sources:
                sys.modules.pop(name, None)

    def guard_recorder(self):
        """Run the production boundary without the external full-runtime provider.

        The pre-fix branch compiles the original capture's unchanged recording
        statements for the red regression. After the fix this executes the new
        complete production helper directly. No original module is patched.
        """
        tree = ast.parse((HERE / 'recovery_worker.py').read_bytes())
        function = next((n for n in tree.body if isinstance(n, ast.FunctionDef) and
                         n.name == 'original_guard_physical_failure'), None)
        if function is None:
            capture = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'runtime_capture')
            start = next(i for i, n in enumerate(capture.body) if isinstance(n, ast.Assign) and
                         any(isinstance(t, ast.Name) and t.id == 'failure' for t in n.targets))
            function = ast.FunctionDef(name='original_guard_physical_failure', args=ast.arguments(
                posonlyargs=[], args=[ast.arg(arg='RC'), ast.arg(arg='old')], vararg=None,
                kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[]),
                body=[*capture.body[start:start+3], ast.Return(value=ast.Name(id='failure', ctx=ast.Load()))],
                decorator_list=[])
        module = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
        namespace = {'require': core.require}
        exec(compile(module, 'recovery_worker.py', 'exec'), namespace)
        return namespace['original_guard_physical_failure']

    def guard_fixture(self, runtime):
        path = self.root / 'old-runtime-root'
        path.mkdir()
        guard = {'schema': 'cell05_connections_runtime_guard_v1', 'all_selected_bytes_rehashed_before_guard': True,
                 'entries': [{'path': str(path), 'lstat': runtime.stat_identity(path)}]}
        return path, guard

    def test_historical_guard_physical_change_is_recorded(self):
        with self.original_runtime_module() as runtime:
            path, guard = self.guard_fixture(runtime)
            path.rename(self.root / 'original-inode')
            path.mkdir()
            escaped, failure = None, None
            try:
                failure = self.guard_recorder()(runtime, guard)
            except Exception as error:
                escaped = error
            self.assertIsNone(escaped, 'Observed physical guard mismatch escaped: ' + repr(escaped))
            self.assertEqual(failure['type'], 'RuntimeError')
            self.assertEqual(failure['message'], 'Current runtime file/directory changed: ' + str(path))

    def test_historical_guard_success_is_not_recovery(self):
        with self.original_runtime_module() as runtime:
            _, guard = self.guard_fixture(runtime)
            with self.assertRaisesRegex(ValueError, 'Expected the observed historical physical-guard failure'):
                self.guard_recorder()(runtime, guard)

    def test_historical_guard_schema_and_duplicates_are_fatal(self):
        with self.original_runtime_module() as runtime:
            _, guard = self.guard_fixture(runtime)
            wrong = copy.deepcopy(guard)
            wrong['schema'] = 'not-an-original-runtime-guard'
            with self.assertRaisesRegex(RuntimeError, 'Invalid runtime guard'):
                self.guard_recorder()(runtime, wrong)
            wrong = copy.deepcopy(guard)
            wrong['entries'].append(copy.deepcopy(wrong['entries'][0]))
            with self.assertRaisesRegex(RuntimeError, 'Duplicate runtime guard path'):
                self.guard_recorder()(runtime, wrong)

    def test_historical_guard_missing_file_is_not_expected_mismatch(self):
        with self.original_runtime_module() as runtime:
            path, guard = self.guard_fixture(runtime)
            path.rmdir()
            with self.assertRaises(FileNotFoundError):
                self.guard_recorder()(runtime, guard)

    def test_exclusive_output_and_external_certificate_pin(self):
        path = self.root / 'CERTIFICATE.json'
        identity = core.write_new(path, {'schema': 'test-certificate', 'value': 'A'})
        self.assertEqual(core.checked(identity)['value'], 'A')
        with self.assertRaises(FileExistsError):
            core.write_new(path, {'value': 'B'})
        before = path.read_bytes()
        path.write_bytes(before.replace(b'"A"', b'"B"'))
        with self.assertRaises(ValueError):
            core.checked(identity)
        # An otherwise valid pin is not allowed to rename the certificate.
        other = self.root / 'other.json'
        other.write_bytes(before)
        with self.assertRaises(ValueError):
            core.checked(identity, other)

    def test_frozen_context_changed_or_omitted_bytes(self):
        original = ORIGINAL / 'verification/remaining9-complete-v1/RUN.json'
        path = self.root / 'historical-context.json'
        path.write_bytes(original.read_bytes())
        identity = core.fp(path)
        value = core.read(path)
        value['context']['environment']['LEAN_NUM_THREADS'] = '2'
        path.write_text(json.dumps(value))
        with self.assertRaises(ValueError):
            core.refs([identity])
        path.unlink()
        with self.assertRaises(ValueError):
            core.refs([identity])

    def test_namespace_addition_and_symlink_rejected(self):
        (self.root / 'A.olean').write_bytes(b'accepted-object')
        before = core.namespace_snapshot(self.root)
        (self.root / 'extra').mkdir()
        self.assertNotEqual(core.namespace_snapshot(self.root), before)
        (self.root / 'extra').rmdir()
        (self.root / 'B.olean').symlink_to(self.root / 'A.olean')
        with self.assertRaises(ValueError):
            core.namespace_snapshot(self.root)

    def test_pinned_source_ignores_pyc_and_rejects_unpinned_import(self):
        source = self.root / 'recovery_test_probe.py'
        source.write_text('VALUE = 911\n')
        py_compile.compile(str(source), cfile=str(self.root / 'recovery_test_probe.pyc'), doraise=True)
        source.write_text('import json\nVALUE = 7\n')
        body = source.read_bytes()
        finder = core.PinnedSourceFinder({'recovery_test_probe': (str(source), body)})
        sys.meta_path.insert(0, finder)
        try:
            module = importlib.import_module('recovery_test_probe')
            self.assertEqual(module.VALUE, 7)
            self.assertIsNone(module.__cached__)
            finder.check_loaded()
            source.write_text('VALUE = 8\n')
            with self.assertRaises(ValueError):
                finder.check_loaded()
        finally:
            sys.meta_path.remove(finder)
            sys.modules.pop('recovery_test_probe', None)
        source.write_text('import recovery_test_unpinned\n')
        (self.root / 'recovery_test_unpinned.py').write_text('VALUE = 1\n')
        finder = core.PinnedSourceFinder({'recovery_test_probe': (str(source), source.read_bytes())})
        sys.meta_path.insert(0, finder)
        sys.path.insert(0, str(self.root))
        try:
            with self.assertRaisesRegex(ValueError, 'Unpinned executable import'):
                importlib.import_module('recovery_test_probe')
        finally:
            sys.path.remove(str(self.root))
            sys.meta_path.remove(finder)
            sys.modules.pop('recovery_test_probe', None)
            sys.modules.pop('recovery_test_unpinned', None)

    def test_family_authentication_checks_all_declared_files(self):
        here = self.root / 'tool'
        here.mkdir()
        rows = []
        for name, body in [('receipt_checks.py', b'PASS = True\n'), ('runtime_compat.py', b'PASS = True\n'),
                           ('helper.py', b'PASS = True\n'), ('SOURCE.json', b'{}\n')]:
            (here / name).write_bytes(body)
            rows.append({'relative_path': name, **core.pin(body)})
        verifier = here / 'VERIFIER.json'
        verifier.write_text(json.dumps({'workflow_files': rows}))
        spec = {'stage': str(self.root), 'tool_relative_path': 'tool', 'verifier_name': verifier.name,
                'verifier': core.fp(verifier)}
        _, _, sources, frozen = core.authenticate_family(spec)
        self.assertEqual(set(sources), {'receipt_checks', 'runtime_compat', 'helper'})
        self.assertEqual(len(frozen), 5)
        (here / 'SOURCE.json').write_bytes(b'[]\n')
        with self.assertRaises(ValueError):
            core.authenticate_family(spec)

    def test_original_remaining8_prefix_counts_reuse_and_gaps(self):
        run = core.read(ORIGINAL / 'verification/remaining9-complete-v1/RUN.json')
        context = run['context']
        pilot = core.read(ORIGINAL / 'verification/remaining9-pilot-v1/STOPPED.json')
        stopped = core.read(ORIGINAL / 'verification/remaining9-complete-v1/STOPPED.json')
        reusable = {(r['module'], m): None for r in context['targets'] for m in ('normal', 'kernel', 'owned')}
        for row in stopped['records']:
            original_path = Path(row['accepted']['path'])
            local = ORIGINAL / original_path.relative_to(context['stage'])
            seal = core.read(local)
            result_path = ORIGINAL / Path(seal['result']['path']).relative_to(context['stage'])
            reusable[row['module'], row['mode']] = {'accepted': row['accepted'], 'result': core.read(result_path)}
        arguments = (context, pilot, stopped, reusable, 8, 'remaining9-pilot-v1', 'remaining9-complete-v1')
        steps, objects = core.check_prefix_index(*arguments)
        self.assertEqual((len(steps), len(objects)), (24, 8))
        for field, value in [('newly_executed_steps', 21), ('reused_steps', 0)]:
            wrong = copy.deepcopy(stopped)
            wrong[field] = value
            with self.assertRaises(ValueError):
                core.check_prefix_index(context, pilot, wrong, *arguments[3:])
        wrong = copy.deepcopy(stopped)
        wrong['records'][0]['disposition'] = 'executed'
        with self.assertRaises(ValueError):
            core.check_prefix_index(context, pilot, wrong, *arguments[3:])
        missing = dict(reusable)
        first = stopped['records'][0]
        missing[first['module'], first['mode']] = None
        with self.assertRaises(ValueError):
            core.check_prefix_index(context, pilot, stopped, missing, *arguments[4:])

    def test_exact_original_source_package_contract(self):
        # Exercise the new glue against the recovered exact original package.
        source = (HERE / 'recovery_worker.py').read_bytes()
        tree = ast.parse(source)
        function = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'package_check')
        ns = {'Path': Path, 'core': core, 'require': core.require, 'checked': core.checked,
              'read': core.read, 'fp': core.fp}
        exec(compile(ast.Module(body=[function], type_ignores=[]), 'recovery_worker.py', 'exec'), ns)
        spec = core.read(HERE / 'ANCHORS.json')['remaining9']
        config = core.read(ORIGINAL / spec['tool_relative_path'] / spec['verifier_name'])
        package = ORIGINAL / 'PACKAGE_CONTENTS.json'
        result = ns['package_check'](package, core.fp(package), 'remaining8', config, spec)
        self.assertEqual(len(result), len(core.read(package)['members']) + 1)
        wrong = copy.deepcopy(config)
        wrong['workflow_files'] = wrong['workflow_files'][1:]
        with self.assertRaisesRegex(ValueError, 'package/workflow inventory differs'):
            ns['package_check'](package, core.fp(package), 'remaining8', wrong, spec)

    def runtime_fixture(self):
        roots = []
        for i in range(10):
            folder = self.root / ('root-%02d' % i)
            folder.mkdir()
            name = 'Example.olean' if i != 9 else 'liblean.so'
            body = ('runtime-%02d' % i).encode()
            (folder / name).write_bytes(body)
            files = [{'relative_path': name, **core.pin(body)}]
            roots.append({'logical_root': 'fixture-%02d' % i, 'physical_root': str(folder),
                          'kind': 'objects' if i != 9 else 'shared', 'files': files,
                          'file_count': 1, 'total_bytes': len(body),
                          'logical_inventory_sha256': hashlib.sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()).hexdigest()})
        snapshot = {'roots': roots}
        summaries = {'P2': {'output': {'path': '/test-only/snapshot.json', 'bytes': 1, 'sha256': '0'*64},
                            'roots': [{k: v for k, v in r.items() if k != 'files'} for r in roots]}}
        namespace = {'Path': Path, 'os': os, 'require': core.require, 'same': core.same,
                     'canonical': lambda p, must_exist=True: core.canonical(str(p), must_exist),
                     'runtime_evidence': lambda here, plan: (summaries, snapshot)}
        probe = {'Path': Path, 'hashlib': hashlib, 'require': core.require,
                 'canonical': lambda p: core.canonical(str(p))}
        authenticated_functions('runtime_probe.py', {'fingerprint', 'selected'}, probe)
        namespace.update(fingerprint=probe['fingerprint'], selected=probe['selected'])
        authenticated_functions('runtime_compat.py', {'stat_identity', 'logical_roots', 'capture_runtime_guard',
                                                     'check_runtime_guard_value'}, namespace)
        return roots, namespace

    def test_real_capture_function_ten_roots_and_content_guard(self):
        roots, ns = self.runtime_fixture()
        guard = ns['capture_runtime_guard'](None, None)
        self.assertEqual(len(guard['logical_roots']), 10)
        self.assertEqual(len(guard['entries']), 20)
        ns['check_runtime_guard_value'](guard)
        path = Path(roots[0]['physical_root']) / roots[0]['files'][0]['relative_path']
        path.write_bytes(b'changed-00')
        with self.assertRaises(ValueError):
            ns['check_runtime_guard_value'](guard)
        with self.assertRaises(ValueError):
            ns['capture_runtime_guard'](None, None)

    def test_real_capture_function_missing_and_extra_selected_files(self):
        roots, ns = self.runtime_fixture()
        path = Path(roots[0]['physical_root']) / roots[0]['files'][0]['relative_path']
        body = path.read_bytes()
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'file inventory changed'):
            ns['capture_runtime_guard'](None, None)
        path.write_bytes(body)
        (path.parent / 'Extra.olean.hash').write_bytes(b'extra')
        with self.assertRaisesRegex(ValueError, 'file inventory changed'):
            ns['capture_runtime_guard'](None, None)

    def test_worker_audit_blocks_write_and_process(self):
        # The hook is irreversible, so exercise it in a separate test interpreter.
        program = """from pathlib import Path
import sys, types, subprocess
p=Path(sys.argv[1]); m=types.ModuleType('audit_test')
exec(compile(p.read_bytes(),str(p),'exec'),m.__dict__)
sys.addaudithook(m.deny_worker_mutation)
denied=0
try: Path(sys.argv[2]).write_bytes(b'not allowed')
except ValueError: denied+=1
try: subprocess.run([sys.executable,'-I','-S','-B','-c','pass'])
except ValueError: denied+=1
assert denied==2
"""
        result = subprocess.run([sys.executable, '-I', '-S', '-B', '-c', program,
                                 str(HERE / 'protocol_core.py'), str(self.root / 'must-not-exist')],
                                capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertFalse((self.root / 'must-not-exist').exists())

    def test_parent_audit_allows_only_authorized_worker_pipes(self):
        worker = self.root / 'harmless_worker.py'
        worker.write_text('import sys\nprint("ok:" + sys.stdin.read(), end="")\n')
        program = """from pathlib import Path
import ast, io, os, stat, subprocess, sys, types
here=Path(sys.argv[1]); WORKER=Path(sys.argv[2]); KINDS=('runtime',)
OUTPUTS={n:WORKER.parent/n for n in ('CURRENT_RUNTIME_GUARD.json','HISTORICAL_VALIDATION.json','CERTIFICATE.json')}
core=types.ModuleType('parent_audit_test')
exec(compile((here/'protocol_core.py').read_bytes(),'protocol_core.py','exec'),core.__dict__)
require=core.require
tree=ast.parse((here/'recovery.py').read_bytes())
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='action_audit')
exec(compile(ast.Module(body=[function],type_ignores=[]),'recovery.py','exec'))
regular=(WORKER.parent/'regular-file').open('w+b')
sys.addaudithook(action_audit('capture'))
result=subprocess.run([sys.executable,'-I','-S','-B',str(WORKER),'runtime'],input=b'{}',stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=5)
assert result.returncode==0 and result.stdout==b'ok:{}' and not result.stderr
denied=0
try: io.open(regular.fileno(),'wb',closefd=False)
except ValueError: denied+=1
try: subprocess.run([sys.executable,'-I','-S','-B',str(WORKER),'not-authorized'],input=b'{}',stdout=subprocess.PIPE,stderr=subprocess.PIPE)
except ValueError: denied+=1
assert denied==2
regular.close()
"""
        result = subprocess.run([sys.executable, '-I', '-S', '-B', '-c', program, str(HERE), str(worker)],
                                capture_output=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr.decode())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--original-stage', type=Path, required=True)
    args, rest = parser.parse_known_args()
    ORIGINAL = args.original_stage.absolute()
    unittest.main(argv=[sys.argv[0], *rest])
