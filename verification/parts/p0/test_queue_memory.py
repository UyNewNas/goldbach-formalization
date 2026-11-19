#!/usr/bin/env python3
"""Queue memory regressions using executable stubs, never installed Lean/Lake."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
QUEUE = 'verification/parts/p0/queue'
PIN = 'f' * 40
COMMIT = 'a' * 40


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def policy(memory):
    return ['-t0', '-j2', f'-M{memory}']


FAKE_TOOL = r'''#!/usr/bin/env python3
import json, os, pathlib, subprocess, sys
name = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
if name == 'elan':
    assert len(args) == 2 and args[0] == 'which', args
    print(pathlib.Path(os.environ['FAKE_BIN']) / args[1])
    sys.exit(0)
if name == 'git':
    if args[0] in ('init', 'remote', 'fetch'):
        sys.exit(0)
    if args[0] == 'checkout':
        source = pathlib.Path('Mathlib/Data/Nat/Basic.lean')
        source.parent.mkdir(parents=True)
        source.write_text('-- fake official source\n')
        sys.exit(0)
    if args[0] == 'rev-parse':
        print(('f' if pathlib.Path.cwd().name == 'mathlib' else 'a') * 40)
        sys.exit(0)
    if args[0] == 'hash-object':
        print('a' * 40)
        sys.exit(0)
    raise RuntimeError('unexpected fake git invocation: ' + repr(args))
if name == 'lake':
    assert args[:4] == ['--no-cache', 'exe', 'cache', 'get'], args
    # Pinned Lake puts the directory of its resolved executable first in PATH.
    # A symlink into the real toolchain bypasses the wrapper; a copy does not.
    child_env = os.environ.copy()
    home = pathlib.Path(__file__).resolve().parent.parent
    child_env['PATH'] = str(home / 'bin') + os.pathsep + child_env['PATH']
    subprocess.run(['lean', *json.loads(os.environ['FAKE_LAKE_LEAN_ARGS'])],
                   env=child_env, check=True)
    package = pathlib.Path('.lake/packages/mathlib')
    for relative in ('.lake/build/bin/cache', '.lake/build/lib/lean/Mathlib/Data/Nat/Basic.olean'):
        output = package / relative
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(b'fake official cache object')
    sys.exit(0)
with open(os.environ['FAKE_EVENTS'], 'a') as output:
    output.write(json.dumps({'name': name, 'args': args,
                             'threads': os.environ.get('LEAN_NUM_THREADS')}) + '\n')
if name == 'lean':
    if args == ['--version']:
        print('Fake Lean for queue tests')
        sys.exit(0)
    if '-o' in args:
        output = pathlib.Path(args[args.index('-o') + 1])
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(('fake compiled object: ' + args[-1]).encode())
    if args[-1].endswith('Audit_Target.lean'):
        print('P0_QUEUE_IMPORTS ' + json.dumps(['Fixture.Target', 'Prereq', 'Mathlib.Data.Nat.Basic', 'Init', 'Lean.Util.CollectAxioms']))
        print('P0_QUEUE_INVENTORY ' + json.dumps({'serialized': ['Fixture.Target.ok'], 'environment': ['Fixture.Target.ok']}))
        print('P0_QUEUE_DECL ' + json.dumps({'name': 'Fixture.Target.ok', 'module': 'Fixture.Target',
              'unsafe': False, 'partial': False, 'axiom': False, 'axioms': [], 'type': 'True'}))
'''


class QueueMemoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='p0-queue-memory-')
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.root = self.base / 'project'
        self.root.mkdir()
        self.bin = self.base / 'toolchain/bin'
        self.bin.mkdir(parents=True)
        self.runner = self.base / 'runner'
        self.runner.mkdir()
        for name in ('lean', 'lake', 'leanchecker', 'leanir', 'clang', 'leanc', 'llvm-ar', 'elan', 'git'):
            executable = self.bin / name
            executable.write_text(FAKE_TOOL)
            executable.chmod(0o755)
        for relative in (
            QUEUE + '/bootstrap.py', QUEUE + '/run.py', QUEUE + '/restore_compiled.py',
            QUEUE + '/AuditTemplate.lean', 'verification/parts/p0/ci_runtime_guard.py',
            'verification/parts/p0/compiler_policy.py',
            'verification/verify_variable_envelope_boxes.py', '.github/workflows/p0-queue.yml',
        ):
            original = ROOT / relative
            # The policy file is deliberately absent on the pre-fix baseline.
            if original.is_file():
                destination = self.root / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(original, destination)
        self.write('verification/parts/p0/check_pins.py', '# Stub pin admission; no network or real tools.\n')
        self.write('lean-toolchain', 'leanprover/lean4:v4.33.0-rc1\n')
        self.write('lakefile.toml', 'name = "queue-memory-fixture"\n')
        self.write_json('lake-manifest.json', {'packages': [
            {'name': 'mathlib', 'rev': PIN, 'url': 'https://example.invalid/mathlib'}]})
        self.write_json('automation/dispatch.json', {'requests': [{'modules': ['Fixture.Target']}]})
        self.write('Fixture/Target.lean', 'import Prereq\ntheorem Target.ok : True := True.intro\n')
        self.write('Prereq.lean', 'import Mathlib.Data.Nat.Basic\n')
        for module in ('Init', 'Lean.Util.CollectAxioms'):
            output = self.bin.parent / 'lib/lean' / (module.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(b'fake bundled object')
        self.events = self.base / 'events.jsonl'
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(('LEAN_', 'LAKE_', 'P0_'))}
        self.env.update(
            PATH=str(self.bin) + os.pathsep + os.environ.get('PATH', ''),
            RUNNER_TEMP=str(self.runner), CHEN_HEAVY_LOCK_PATH=str(self.base / 'heavy.lock'),
            FAKE_BIN=str(self.bin), FAKE_EVENTS=str(self.events),
            P0_DEPENDENCY_MODE='FRESH_PINNED_TARGET_CLOSURE',
            FAKE_LAKE_LEAN_ARGS=json.dumps([
                '-t5', '--trust=7', '-j8', '--threads', '9',
                '-M', '4096', '--memory=4096', '--memory', '4096', '-qM4096',
                '-DwarningAsError=true', '--timeout=60', '-o', 'Cache.olean', 'Cache.lean']),
        )

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def write_json(self, relative, value):
        return self.write(relative, json.dumps(value, indent=2) + '\n')

    def read_json(self, relative):
        return json.loads((self.root / relative).read_text())

    def invoke(self, name, *arguments):
        return subprocess.run([sys.executable, str(self.root / QUEUE / name), *map(str, arguments)],
                              cwd=self.root, env=self.env, capture_output=True, text=True, timeout=20)

    def records(self):
        return [json.loads(line) for line in self.events.read_text().splitlines()] if self.events.exists() else []

    def package(self):
        self.write('.lake/packages/mathlib/Mathlib/Data/Nat/Basic.lean', '-- fake official source\n')
        self.write('.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Basic.olean', 'fake official object')

    def bootstrap_receipt(self, memory=12288):
        return self.write_json('.lake/p0-queue/bootstrap/receipt.json', {
            'status': 'PASS_OFFICIAL_CACHE_ONLY',
            'manifest_sha256': digest(self.root / 'lake-manifest.json'),
            'command_policy': policy(memory), 'lean_memory_mb': memory,
            'target_source_walk': {module: {'path': module.replace('.', '/') + '.lean',
                                           'sha256': digest(self.root / (module.replace('.', '/') + '.lean'))}
                                   for module in ('Fixture.Target', 'Prereq')},
        })

    def assert_runner_policy(self, memory):
        self.package()
        self.bootstrap_receipt(memory)
        request = self.write_json('request.json', {'run_id': 'memory-test', 'modules': ['Fixture.Target']})
        result = self.invoke('run.py', request)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        expected = policy(memory)
        receipt = self.read_json('.lake/p0-queue/memory-test/receipt.json')
        self.assertEqual(receipt['status'], 'PASS_SCOPED_LEAVES')
        records = self.records()
        compiles = [r for r in records if r['name'] == 'lean' and '-o' in r['args']]
        self.assertEqual(len(compiles), 3)
        for record in compiles:
            self.assertEqual(record['args'][:3], expected)
            self.assertEqual(record['threads'], '2')
            self.assertEqual([a for a in record['args'] if a.startswith('-M')], [f'-M{memory}'])
        for record in compiles:
            self.assertEqual('-DwarningAsError=true' in record['args'],
                             record['args'][-1] != 'Prereq.lean')
        checkers = [r for r in records if r['name'] == 'leanchecker']
        self.assertEqual([r['args'] for r in checkers],
                         [['--verbose', 'Fixture.Target'], ['--verbose', 'verification.parts.p0.queue.Audit_Target']])
        self.assertTrue(all(r['threads'] == '2' for r in checkers))
        self.assertEqual(receipt['command_policy'], expected)
        self.assertEqual(receipt['lean_memory_mb'], memory)
        stages = [s for s in receipt['stages'] if s['label'].startswith(('compile-', 'audit-'))
                  and not s['label'].startswith('audit-replay-')]
        self.assertEqual([s['command'][1:] for s in stages], [r['args'] for r in compiles])
        index = self.read_json('.lake/p0-queue/fresh-index.json')
        self.assertEqual(set(index), {'Prereq', 'Fixture.Target'})
        for entry in index.values():
            self.assertEqual(entry['inputs']['command_policy'], expected)

    def test_default_memory_reaches_compile_audit_receipt_and_index(self):
        self.assert_runner_policy(12288)

    def test_raised_memory_reaches_compile_audit_receipt_and_index(self):
        self.env['P0_LEAN_MEMORY_MB'] = '16384'
        self.assert_runner_policy(16384)

    def test_runner_rejects_bootstrap_memory_mismatch_before_compiling(self):
        self.package()
        self.bootstrap_receipt(12288)
        self.env['P0_LEAN_MEMORY_MB'] = '16384'
        request = self.write_json('request.json', {'run_id': 'mismatch', 'modules': ['Fixture.Target']})
        result = self.invoke('run.py', request)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = self.read_json('.lake/p0-queue/mismatch/receipt.json')
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertIn('bootstrap', receipt['failure'].lower())
        self.assertFalse(any(r['name'] == 'lean' and '-o' in r['args'] for r in self.records()))

    def assert_bootstrap_policy(self, memory):
        result = self.invoke('bootstrap.py')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        records = [r for r in self.records() if r['name'] == 'lean']
        self.assertEqual(len(records), 1)
        expected = policy(memory) + ['-q', '-D', 'warningAsError=true', '--timeout=60',
                                     '-o', 'Cache.olean', 'Cache.lean']
        self.assertEqual(records[0]['args'], expected)
        self.assertEqual(records[0]['threads'], '2')
        receipt = self.read_json('.lake/p0-queue/bootstrap/receipt.json')
        self.assertEqual(receipt['status'], 'PASS_OFFICIAL_CACHE_ONLY')
        self.assertEqual(receipt['command_policy'], policy(memory))
        self.assertEqual(receipt['lean_memory_mb'], memory)
        log = self.root / '.lake/p0-queue/bootstrap/compiler-commands.jsonl'
        commands = [json.loads(line)['command'] for line in log.read_text().splitlines()]
        self.assertEqual(commands, [[str(self.bin / 'lean'), *expected]])

    def test_bootstrap_default_memory_normalizes_split_long_and_cluster_overrides(self):
        self.assert_bootstrap_policy(12288)

    def test_bootstrap_raised_memory_normalizes_split_long_and_cluster_overrides(self):
        self.env['P0_LEAN_MEMORY_MB'] = '16384'
        self.assert_bootstrap_policy(16384)

    def artifact(self, memory, stage_memory=None, stage_suffix=()):
        self.bootstrap_receipt()
        producer_runner = 'b' * 64
        objects = {str(self.root / '.lake/p0-queue/fresh-objects/Prereq.olean'):
                   hashlib.sha256(b'archived prerequisite').hexdigest()}
        entry = {
            'inputs': {'source_sha256': digest(self.root / 'Prereq.lean'),
                       'dependency_objects': {},
                       'pins': {p: digest(self.root / p)
                                for p in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')},
                       'lean_sha256': digest(self.bin / 'lean'), 'command_policy': policy(memory)},
            'objects': objects, 'producer_run_id': 'producer', 'replayed': False,
        }
        producer = {'source_commit': COMMIT, 'run_id': 'producer',
                    'status': 'PASS_SCOPED_LEAVES', 'command_policy': policy(memory), 'lean_memory_mb': memory,
                    'verifier_sha256': {QUEUE + '/run.py': producer_runner},
                    'compiled_objects': {'Prereq': objects},
                    'stages': [{'label': 'compile-Prereq', 'exit_code': 0,
                                'command': [str(self.bin / 'lean'),
                                            *policy(memory if stage_memory is None else stage_memory),
                                            *stage_suffix,
                                            '-o', next(iter(objects)), 'Prereq.lean']}]}
        index_bytes = json.dumps({'Prereq': entry}).encode()
        receipt_bytes = json.dumps(producer).encode()
        archive = self.base / 'artifact.zip'
        with zipfile.ZipFile(archive, 'w') as output:
            output.writestr('fresh-index.json', index_bytes)
            output.writestr('producer/receipt.json', receipt_bytes)
            output.writestr('fresh-objects/Prereq.olean', b'archived prerequisite')
        anchor = {'artifact_id': 7, 'repository': 'UyNewNas/goldbach-formalization',
                  'run_id': 17, 'attempt': 1, 'source_commit': COMMIT,
                  'producer_runner_sha256': producer_runner, 'artifact_sha256': digest(archive),
                  'fresh_index_sha256': hashlib.sha256(index_bytes).hexdigest(),
                  'receipt_sha256': {'producer/receipt.json': hashlib.sha256(receipt_bytes).hexdigest()}}
        self.write_json(QUEUE + '/reuse-anchors.json', {'artifacts': {'7': anchor}})
        self.write_json('automation/dispatch.json', {'requests': [{'modules': ['Fixture.Target']}],
                                                     'reuse_artifact_ids': [7]})
        return archive, entry

    def test_restore_skips_legacy_4gib_identity_without_relabeling(self):
        archive, _ = self.artifact(4096)
        before = digest(archive)
        result = self.invoke('restore_compiled.py', archive)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.read_json('.lake/p0-queue/fresh-index.json'), {})
        self.assertFalse((self.root / '.lake/p0-queue/fresh-objects/Prereq.olean').exists())
        receipt = self.read_json('.lake/p0-queue/reuse-staging.json')
        self.assertIn('7:Prereq', receipt['skipped_modules'])
        self.assertEqual(receipt['restored_modules'], [])
        self.assertEqual(receipt['command_policy'], policy(12288))
        self.assertEqual(receipt['lean_memory_mb'], 12288)
        self.assertEqual(digest(archive), before)

    def test_restore_accepts_current_policy_and_preserves_bound_identity(self):
        archive, entry = self.artifact(12288)
        result = self.invoke('restore_compiled.py', archive)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        restored = self.read_json('.lake/p0-queue/fresh-index.json')
        self.assertEqual(set(restored), {'Prereq'})
        self.assertEqual(restored['Prereq']['inputs'], entry['inputs'])
        self.assertEqual(restored['Prereq']['objects'], entry['objects'])
        self.assertEqual(restored['Prereq']['verification_level'], 'COMPILED_NOT_REPLAYED')
        self.assertEqual((self.root / '.lake/p0-queue/fresh-objects/Prereq.olean').read_bytes(),
                         b'archived prerequisite')
        receipt = self.read_json('.lake/p0-queue/reuse-staging.json')
        self.assertEqual(receipt['restored_modules'], ['Prereq'])
        self.assertEqual(receipt['command_policy'], policy(12288))
        self.assertEqual(receipt['lean_memory_mb'], 12288)
        self.assertEqual(receipt['normalizer_sha256'],
                         digest(self.root / 'verification/parts/p0/ci_runtime_guard.py'))
        self.assertEqual(receipt['compiler_policy_sha256'],
                         digest(self.root / 'verification/parts/p0/compiler_policy.py'))

    def test_restore_rejects_producer_stage_that_disagrees_with_current_signature(self):
        for memory, suffix in ((4096, ()), (12288, ('--memory=4096',)), (12288, ('-qM4096',))):
            with self.subTest(stage_memory=memory, stage_suffix=suffix):
                try:
                    archive, _ = self.artifact(12288, stage_memory=memory, stage_suffix=suffix)
                    result = self.invoke('restore_compiled.py', archive)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    expected_failure = ('resource override after frozen compiler policy' if suffix else
                                        'Producer compiler command differs from its signature')
                    self.assertIn(expected_failure, result.stderr)
                    self.assertFalse((self.root / '.lake/p0-queue/fresh-objects/Prereq.olean').exists())
                finally:
                    # Give each archive an independent extraction/restore destination.
                    shutil.rmtree(self.root / '.lake/p0-reuse-input-7', ignore_errors=True)
                    shutil.rmtree(self.root / '.lake/p0-queue/fresh-objects', ignore_errors=True)
                    (self.root / '.lake/p0-queue/fresh-index.json').unlink(missing_ok=True)
                    (self.root / '.lake/p0-queue/reuse-staging.json').unlink(missing_ok=True)


if __name__ == '__main__':
    unittest.main()
