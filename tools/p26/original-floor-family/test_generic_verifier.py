#!/usr/bin/env python3
"""Four local boundary tests. Synthetic Python commands only; never Lean."""
from pathlib import Path
import errno
import importlib.util
import json
import os
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


v = load('generic_verifier_tested', HERE / 'GenericFloor_verify.py')
shared = load('generic_fixture_shared', REPO / 'tools/p26/Cell00OriginalFloor_continue.py')
owned = load('generic_fixture_owned', REPO / 'tools/p26/export_cell01_row000.py')


class Fixture:
    """Real receipt serialization around an explicit non-Lean Python shim."""
    def __init__(self, root):
        self.root = root
        self.stage = root / 'stage'
        self.project = self.stage / 'project'
        self.objects = self.stage / 'objects'
        self.project.mkdir(parents=True)
        self.objects.mkdir()
        self.source = self.project / v.module_relative(v.TARGET, '.lean')
        self.source.parent.mkdir()
        self.source.write_bytes((REPO / v.module_relative(v.TARGET, '.lean')).read_bytes())
        self.audit = self.stage / 'audit' / 'fixture-audit.lean'
        self.audit.parent.mkdir()
        self.audit.write_bytes((HERE / 'owned-audit.lean').read_bytes())
        self.obj = self.objects / v.module_relative(v.TARGET)
        self.obj.parent.mkdir()
        self.runtime = root / 'runtime'
        self.runtime.mkdir()
        (self.runtime / 'fixed.bin').write_bytes(b'fixed runtime bytes')
        self.shim = root / 'synthetic-python-compiler'
        self.shim.write_text("""#!/usr/bin/env python3
from pathlib import Path
import sys
r=Path(__file__).parent
mode='normal' if '-o' in sys.argv else 'kernel' if '--verbose' in sys.argv else 'owned'
if (r/'fail-mode').exists() and (r/'fail-mode').read_text()==mode:
    print('synthetic failed step',file=sys.stderr)
    sys.exit(7)
if mode=='normal':
    Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'SYNTHETIC_OBJECT_NOT_LEAN')
    p=r/'normal-count'
    p.write_text(str(int(p.read_text())+1 if p.exists() else 1))
elif mode=='owned':
    print((r/'synthetic-owned.log').read_text(),end='')
else:
    print('synthetic kernel command, not Lean')
""")
        self.shim.chmod(0o755)
        declaration = {'name': v.TARGET + '.synthetic_fixture', 'module': v.TARGET,
                       'unsafe': False, 'partial': False, 'axiom': False,
                       'type': 'True', 'axioms': []}
        names = [declaration['name']]
        rows = [('IMPORTS', [v.TARGET]),
                ('INVENTORY', {'module': v.TARGET, 'serialized': names, 'environment': names}),
                ('DECL', declaration), ('COMPLETE', {'module': v.TARGET, 'count': 1})]
        self.owned_text = ''.join('P26_GEOMETRY01_AUDIT_' + name + ' ' + json.dumps(data) + '\n'
                                  for name, data in rows)
        (root / 'synthetic-owned.log').write_text(self.owned_text)
        self.inputs = {'files': [], 'installed_files': [], 'synthetic_fixture': True}
        v.write_json(self.stage, self.stage / 'INPUT_FINGERPRINTS.json', self.inputs)
        self.context = {'synthetic_fixture': True, 'stage': str(self.stage), 'module': v.TARGET,
            'project': str(self.project), 'objects': str(self.objects),
            'inputs': v.fp(self.stage / 'INPUT_FINGERPRINTS.json'),
            'LEAN_PATH': str(self.objects), 'lean_binary': v.fp(self.shim),
            'leanchecker_binary': v.fp(self.shim),
            'runtime_roots': [str(self.runtime)], 'runtime_trees': [v.tree_signature(self.runtime)],
            'project_modules': [v.TARGET], 'module_search_roots': [str(self.objects)]}
        v.write_json(self.stage, self.stage / 'CONTEXT.json', self.context)
        self.context_pin = v.fp(self.stage / 'CONTEXT.json')
        self.frozen = v.Frozen()
        self.frozen.add(self.source)
        self.frozen.add(self.audit)

    def run(self, mode, attempt_name='first'):
        attempt = self.stage / 'attempts' / attempt_name
        v.mkdir(self.stage, attempt)
        run = {'synthetic_fixture': True, 'stage': str(self.stage), 'module': v.TARGET,
               'stage_context': self.context_pin, 'inputs': self.context['inputs'],
               'project': str(self.project), 'LEAN_PATH': self.context['LEAN_PATH'],
               'source': v.fp(self.source), 'audit': v.fp(self.audit),
               'object_path': str(self.obj), 'lean': str(self.shim), 'checker': str(self.shim),
               'rss_gib': 6, 'wall_seconds': 30}
        run_pin = v.keep_json(self.stage, attempt / 'RUN.json', run)
        before = v.recheck(self.stage, attempt / 'checks' / (mode + '-before.json'),
                          self.context, self.context_pin, self.frozen)
        live = v.object_state(self.stage, self.obj)
        folder = attempt / 'steps' / mode
        v.mkdir(self.stage, folder.parent)
        metadata = {'module': v.TARGET, 'mode': mode, 'run': run_pin,
                    'context': self.context_pin, 'source': v.fp(self.source), 'audit': v.fp(self.audit),
                    'object_before': live['object'], 'input_fingerprints': self.context['inputs']}
        env = dict(os.environ, LEAN_PATH=run['LEAN_PATH'])
        result = shared.run_command(v.expected_argv(mode, run), self.project, env, folder, 30, metadata)
        after = v.recheck(self.stage, attempt / 'checks' / (mode + '-after.json'),
                         self.context, self.context_pin, self.frozen)
        state = v.object_state(self.stage, self.obj)
        seal = {'status': 'succeeded', 'module': v.TARGET, 'mode': mode,
                'source': v.fp(self.source), 'audit': v.fp(self.audit), 'object': state['object'],
                'object_sidecars': state['sidecars'], 'run': run_pin, 'context': self.context_pin,
                'command': v.fp(folder / 'command.json'), 'command_result': v.fp(folder / 'result.json'),
                'log': result['log'], 'before': before, 'after': after}
        if mode == 'normal':
            seal['printed_axioms'] = []
        if mode == 'owned':
            data = owned.parse_owned(Path(result['log']['path']).read_text(), v.TARGET)
            imports = v.parsed_imports(Path(result['log']['path']).read_text(), [v.TARGET])
            byte_context = v.module_byte_context(imports, [self.objects])
            v.write_json(self.stage, folder / 'owned-declarations.json', data)
            v.write_json(self.stage, folder / 'module-byte-context.json', byte_context)
            seal.update({'owned_declarations': v.fp(folder / 'owned-declarations.json'),
                         'module_byte_context': v.fp(folder / 'module-byte-context.json'),
                         'owned_declaration_count': 1})
        v.write_json(self.stage, folder / 'ACCEPTED_STEP.json', seal)
        v.validate_step(folder / 'ACCEPTED_STEP.json', self.stage, self.context_pin,
                        v.fp(self.source), v.fp(self.audit), self.obj, owned)
        return folder

    def scan(self):
        return v.scan_history(self.stage, self.context_pin, v.fp(self.source),
                              v.fp(self.audit), self.obj, owned)


class GenericBoundaries(unittest.TestCase):
    def test_path_isolation_and_no_object_copy_fallback(self):
        with tempfile.TemporaryDirectory(prefix='p26-generic-path-') as tmp:
            root = Path(tmp).resolve()
            stage, outside, provider = root / 'stage', root / 'outside', root / 'provider'
            stage.mkdir(); outside.mkdir(); provider.mkdir()
            source = provider / 'fixture.olean'; source.write_bytes(b'old pinned fixture')
            (stage / 'objects').symlink_to(outside, target_is_directory=True)
            with self.assertRaises(RuntimeError):
                v.install_link(stage, source, stage / 'objects' / 'missing.olean', v.fp(source))
            self.assertEqual(list(outside.iterdir()), [])
            for a, b in [(stage, stage), (stage, stage / 'child'), (stage / 'child', stage)]:
                with self.assertRaises(RuntimeError):
                    v.disjoint(a, b)
            (stage / 'objects').unlink(); (stage / 'objects').mkdir()
            (stage / 'objects/dangling.olean').symlink_to(outside / 'missing.olean')
            with self.assertRaises(RuntimeError):
                v.install_link(stage, source, stage / 'objects/dangling.olean', v.fp(source))
            destination = stage / 'objects/linked.olean'
            v.install_link(stage, source, destination, v.fp(source))
            self.assertEqual(source.stat().st_ino, destination.stat().st_ino)
            with mock.patch.object(v.os, 'link', side_effect=OSError(errno.EXDEV, 'cross-device')):
                with self.assertRaises(OSError):
                    v.install_link(stage, source, stage / 'objects/not-copied.olean', v.fp(source))
            self.assertFalse((stage / 'objects/not-copied.olean').exists())

    def test_source_and_runtime_bytes_are_rechecked_before_acceptance(self):
        with tempfile.TemporaryDirectory(prefix='p26-generic-freeze-') as tmp:
            f = Fixture(Path(tmp).resolve())
            saved = f.source.read_bytes()
            f.source.write_bytes(saved + b'\n')
            with self.assertRaises(RuntimeError):
                v.recheck(f.stage, f.stage / 'changed-source.json', f.context, f.context_pin, f.frozen)
            self.assertFalse((f.stage / 'changed-source.json').exists())
            f.source.write_bytes(saved)
            (f.runtime / 'fixed.bin').write_bytes(b'changed runtime bytes')
            with self.assertRaisesRegex(RuntimeError, 'Runtime module byte context changed'):
                v.recheck(f.stage, f.stage / 'changed-runtime.json', f.context, f.context_pin, f.frozen)
            self.assertFalse((f.stage / 'changed-runtime.json').exists())

    def test_accepted_or_successful_normal_damage_never_becomes_a_rerun(self):
        with tempfile.TemporaryDirectory(prefix='p26-generic-reuse-') as tmp:
            f = Fixture(Path(tmp).resolve())
            folder = f.run('normal')
            self.assertEqual(set(f.scan()), {'normal'})
            for path in [f.obj, folder / 'result.json', folder / 'output.log']:
                with self.subTest(missing=str(path)):
                    saved = path.read_bytes(); path.unlink()
                    with self.assertRaises(RuntimeError):
                        f.scan()
                    path.write_bytes(saved)
            (f.stage / 'accepted/normal.json').unlink()
            (folder / 'ACCEPTED_STEP.json').unlink()
            with self.assertRaisesRegex(RuntimeError, 'RESTORE_SUCCESS_EVIDENCE_CHAIN'):
                f.scan()
            self.assertEqual((f.root / 'normal-count').read_text(), '1')
        with tempfile.TemporaryDirectory(prefix='p26-generic-unreceipted-') as tmp:
            f = Fixture(Path(tmp).resolve())
            f.obj.write_bytes(b'unreceipted object')
            with self.assertRaisesRegex(RuntimeError, 'UNRECEIPTED_OBJECT'):
                f.scan()

    def test_failed_steps_resume_and_owned_export_keeps_supplier_bodies_out(self):
        with tempfile.TemporaryDirectory(prefix='p26-generic-resume-') as tmp:
            f = Fixture(Path(tmp).resolve())
            f.run('normal')
            (f.root / 'fail-mode').write_text('kernel')
            with self.assertRaises(shared.VerificationError):
                f.run('kernel')
            (f.root / 'fail-mode').unlink()
            self.assertEqual(set(f.scan()), {'normal'})
            self.assertTrue((f.stage / 'attempts/first/steps/kernel/result.json').exists())
            f.run('kernel', 'second')
            f.run('owned', 'second')
            accepted = f.scan()
            self.assertEqual(set(accepted), set(v.MODES))
            self.assertEqual(f.scan(), accepted)
            self.assertEqual((f.root / 'normal-count').read_text(), '1')
            bad = f.owned_text.replace('"type": "True"', '"type": "\\u22ef"')
            with self.assertRaises(RuntimeError):
                owned.parse_owned(bad, v.TARGET)
            (f.objects / 'ImbalancedChen/FrozenSupplier.olean').write_bytes(b'OLD_SUPPLIER_BODY_NOT_EXPORTED')
            package = f.root / 'package'; package.mkdir()
            (package / 'fixture.txt').write_text('synthetic frozen package')
            pin = v.fp(package / 'fixture.txt')
            (package / 'PACKAGE_MANIFEST.json').write_text(json.dumps(
                {'files': [{'member': 'fixture.txt', **pin}]}))
            result = v.archive_success(f.stage, package, f.stage / 'attempts/second',
                                       f.context_pin, f.source, f.audit, f.obj)
            with tarfile.open(result['archive']['path']) as archive:
                objects = [m for m in archive.getmembers() if m.name.endswith('.olean')]
                self.assertEqual(len(objects), 1)
                self.assertEqual(objects[0].name, str(f.obj.relative_to(f.stage)))
                self.assertFalse(any('FrozenSupplier' in m.name for m in archive.getmembers()))


if __name__ == '__main__':
    unittest.main(verbosity=2)
