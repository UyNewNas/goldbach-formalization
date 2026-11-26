#!/usr/bin/env python3
"""Six local boundary tests: four prior checks plus the two reviewed regressions.

Every command is an explicitly synthetic Python shim. This never invokes Lean.
The v1 test source and driver are imported without modifying their bytes.
"""
from pathlib import Path
import hashlib
import json
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import test_generic_verifier as base

v = base.load('generic_verifier_v2_tested', HERE / 'GenericFloor_verify_v2.py')
base.v = v
Fixture, shared, owned = base.Fixture, base.shared, base.owned


def package_fixture(f):
    package = f.root / 'package'
    package.mkdir()
    (package / 'fixture.txt').write_text('synthetic frozen package')
    pin = v.fp(package / 'fixture.txt')
    (package / 'PACKAGE_MANIFEST.json').write_text(json.dumps(
        {'files': [{'member': 'fixture.txt', **pin}]}))
    return package


def export_check(f, calls):
    """Validate the real synthetic chains and frozen fixture runtime at export."""
    def check():
        accepted = f.scan()
        v.need(set(accepted) == set(v.MODES), 'Incomplete synthetic accepted chains')
        f.frozen.check()
        v.pinned(f.stage / 'CONTEXT.json', f.context_pin)
        v.pinned(f.stage / 'INPUT_FINGERPRINTS.json', f.context['inputs'])
        v.need([v.tree_signature(root) for root in f.context['runtime_roots']] ==
               f.context['runtime_trees'], 'Synthetic runtime changed')
        calls.append(len(calls) + 1)
        return {'synthetic_fixture': True, 'all_three_chains_checked': True,
                'runtime_and_frozen_files_checked': True, 'call': calls[-1],
                'records': [{'mode': mode, 'receipt': accepted[mode]} for mode in v.MODES]}
    return check


class GenericBoundariesV2(base.GenericBoundaries):
    def test_failed_steps_resume_and_owned_export_keeps_supplier_bodies_out(self):
        # The original fourth check, now requiring both export-boundary callbacks.
        with tempfile.TemporaryDirectory(prefix='p26-generic-v2-resume-') as tmp:
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
            package, calls = package_fixture(f), []
            result = v.archive_success(f.stage, package, f.stage / 'attempts/second',
                                       f.context_pin, f.source, f.audit, f.obj,
                                       final_check=export_check(f, calls))
            self.assertEqual(calls, [1, 2])
            self.assertEqual(result['archive_readback'],
                             'EXACT_REGULAR_UNIQUE_INVENTORY_SIZE_SHA256_VERIFIED')
            self.assertTrue(result['selected_input_pins_unchanged_after_packing'])
            self.assertEqual(result['post_export_validation']['call'], 2)
            with tarfile.open(result['archive']['path']) as archive:
                members = archive.getmembers()
                objects = [m for m in members if m.name.endswith('.olean')]
                self.assertEqual(len(objects), 1)
                self.assertEqual(objects[0].name, str(f.obj.relative_to(f.stage)))
                self.assertFalse(any('FrozenSupplier' in m.name for m in members))
                manifest = json.load(archive.extractfile('MANIFEST.json'))
                self.assertEqual({m.name for m in members},
                                 {r['member'] for r in manifest['files']} | {'MANIFEST.json'})
                for row in manifest['files']:
                    payload = archive.extractfile(row['member']).read()
                    self.assertEqual(len(payload), row['bytes'])
                    self.assertEqual(hashlib.sha256(payload).hexdigest(), row['sha256'])

    def test_failed_attempt_index_cannot_hide_lost_accepted_normal(self):
        # Review I1: the failed RESULT is the only surviving acceptance reference.
        with tempfile.TemporaryDirectory(prefix='p26-generic-v2-index-') as tmp:
            f = Fixture(Path(tmp).resolve())
            folder = f.run('normal')
            accepted = f.scan()
            result_path = f.stage / 'attempts/first/RESULT.json'
            value = {'status': 'FAILED_STOPPED', 'context': f.context_pin,
                     'records': [{'mode': 'normal', 'receipt': accepted['normal'], 'reused': False}],
                     'new_proof_commands': 2, 'supplier_proof_commands': 0}
            result_path.write_text(json.dumps(value))
            self.assertEqual(f.scan(), accepted)
            for modes in [('normal', 'normal'), ('kernel',), ('unknown',)]:
                with self.subTest(modes=modes):
                    malformed = {**value, 'records': [
                        {'mode': mode, 'receipt': accepted['normal']} for mode in modes]}
                    result_path.write_text(json.dumps(malformed))
                    with self.assertRaisesRegex(RuntimeError, 'duplicate, unknown, or out of order'):
                        f.scan()
            result_path.write_text(json.dumps(value))
            for path in [f.stage / 'accepted/normal.json', folder / 'ACCEPTED_STEP.json',
                         folder / 'result.json', f.obj]:
                path.unlink()
            with self.assertRaisesRegex(RuntimeError, 'RESTORE_ACCEPTED_INDEX_CHAIN'):
                f.scan()
            self.assertEqual((f.root / 'normal-count').read_text(), '1')
            self.assertFalse((f.stage / 'accepted/normal.json').exists())

    def test_archive_rejects_same_length_object_mutation_during_addfile(self):
        # Review I2: mutation after the per-member precheck and before tar reads it.
        with tempfile.TemporaryDirectory(prefix='p26-generic-v2-tar-drift-') as tmp:
            f = Fixture(Path(tmp).resolve())
            for mode in v.MODES:
                f.run(mode)
            f.scan()
            package, calls, mutations = package_fixture(f), [], []
            original_addfile = v.tarfile.TarFile.addfile
            target_member = str(f.obj.relative_to(f.stage))
            def mutate_before_read(archive, info, fileobj=None):
                if info.name == target_member:
                    before = v.fp(f.obj)
                    f.obj.write_bytes(b'X' * before['bytes'])
                    mutations.append((before, v.fp(f.obj)))
                return original_addfile(archive, info, fileobj)
            with mock.patch.object(v.tarfile.TarFile, 'addfile', new=mutate_before_read):
                with self.assertRaisesRegex(RuntimeError, 'archive payload differs from frozen input'):
                    v.archive_success(f.stage, package, f.stage / 'attempts/first',
                                      f.context_pin, f.source, f.audit, f.obj,
                                      final_check=export_check(f, calls))
            self.assertEqual(len(mutations), 1)
            self.assertEqual(mutations[0][0]['bytes'], mutations[0][1]['bytes'])
            self.assertNotEqual(mutations[0][0]['sha256'], mutations[0][1]['sha256'])
            self.assertEqual(calls, [1])
            self.assertEqual((f.root / 'normal-count').read_text(), '1')
            self.assertTrue((f.stage / 'evidence/first.tar.xz').exists())
            self.assertFalse((f.stage / 'evidence/first.tar.manifest.json').exists())
            self.assertFalse((f.stage / 'attempts/first/RESULT.json').exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
