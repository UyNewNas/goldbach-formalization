#!/usr/bin/env python3
"""Regression tests for I1 write isolation and I2 accepted-object preservation only."""
from pathlib import Path
import ast
import contextlib
import hashlib
import importlib.util
import io
import json
import os
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path[:0] = [str(HERE), str(HERE.parent)]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

driver = load('p26_batch_boundary_driver', HERE / 'Cell01Batch_verify.py')
stager = load('p26_batch_boundary_stager', HERE / 'stage_batch.py')

def tree_state(root):
    result = []
    for path in sorted(root.rglob('*')):
        rel = str(path.relative_to(root))
        if path.is_symlink():
            result.append((rel, 'symlink', os.readlink(path)))
        elif path.is_file():
            result.append((rel, 'file', hashlib.sha256(path.read_bytes()).hexdigest()))
        elif path.is_dir():
            result.append((rel, 'directory'))
    return result

class BoundaryTests(unittest.TestCase):
    def test_I1_no_write_through_symlinks_or_overlapping_roots(self):
        with tempfile.TemporaryDirectory(prefix='p26-boundary-I1-') as name:
            root = Path(name).resolve()
            repo, base = root / 'repo', root / 'base-parent' / 'base'
            repo.mkdir(); base.mkdir(parents=True)
            payload = repo / 'payload.txt'; payload.write_text('frozen fixture\n')
            plan = {'new_proof_owners':142, 'supplier_objects_included':False, 'files':[
                {'origin':'repo', 'relative_source':'payload.txt',
                 'archive_member':'project/payload.txt', **stager.fp(payload)}]}
            plan_path=repo/'tools/p26/cell01-rest/STAGING_PLAN.json'
            plan_path.parent.mkdir(parents=True)
            plan_path.write_text(json.dumps(plan))

            def stage_call(stage, *extra):
                argv=['stage_batch.py','--repo',str(repo),'--base-stage',str(base),
                      '--stage',str(stage),*extra]
                with mock.patch.object(sys, 'argv', argv), contextlib.redirect_stdout(io.StringIO()):
                    stager.main()

            for stage in [repo, base, repo/'nested-stage', base/'nested-stage',
                          repo.parent, base.parent]:
                with self.subTest(overlap=str(stage)):
                    before=tree_state(root)
                    with self.assertRaises(ValueError):
                        stage_call(stage)
                    self.assertEqual(tree_state(root),before)

            outside=root/'outside'; outside.mkdir()
            escaped=root/'stage-parent-link'; escaped.mkdir()
            (escaped/'project').symlink_to(outside,target_is_directory=True)
            before=tree_state(root)
            with self.assertRaises(ValueError):
                stage_call(escaped)
            self.assertEqual(tree_state(root),before)

            dangling=root/'stage-dangling'; (dangling/'project').mkdir(parents=True)
            (dangling/'project/payload.txt').symlink_to(outside/'absent.txt')
            before=tree_state(root)
            with self.assertRaises(ValueError):
                stage_call(dangling)
            self.assertEqual(tree_state(root),before)

            valid=root/'valid-stage'
            stage_call(valid)
            self.assertEqual((valid/'project/payload.txt').read_bytes(),payload.read_bytes())
            before=tree_state(root)
            stage_call(valid,'--check-only')
            self.assertEqual(tree_state(root),before)

            supplier=root/'supplier.bin'; supplier.write_bytes(b'pinned supplier')
            cache=root/'cache'; cache.mkdir()
            for child in ['objects','verification']:
                stage=root/('driver-root-'+child)
                (stage/'project').mkdir(parents=True)
                (stage/child).symlink_to(outside,target_is_directory=True)
                before=tree_state(root)
                argv=['Cell01Batch_verify.py','--stage',str(stage),
                      '--cache-root',str(cache),'--rows','2']
                with mock.patch.object(sys,'argv',argv), \
                     mock.patch.object(driver.subprocess,'run',
                         side_effect=AssertionError('No external command is allowed in this test')), \
                     self.assertRaises(ValueError):
                    driver.main()
                self.assertEqual(tree_state(root),before)

            install=root/'install-stage'; (install/'objects').mkdir(parents=True)
            (install/'objects/ImbalancedChen').symlink_to(outside,target_is_directory=True)
            before=tree_state(root)
            with self.assertRaises(ValueError):
                driver.install_frozen_file(supplier,
                    install/'objects/ImbalancedChen/fixture.olean',
                    driver.fp(supplier),stage=install)
            self.assertEqual(tree_state(root),before)
            with self.assertRaises(ValueError):
                driver.install_frozen_file(supplier,outside/'fixture.olean',
                    driver.fp(supplier),stage=install)
            self.assertEqual(tree_state(root),before)
            (install/'objects/dangling.olean').symlink_to(outside/'missing.olean')
            before=tree_state(root)
            with self.assertRaises(ValueError):
                driver.install_frozen_file(supplier,install/'objects/dangling.olean',
                    driver.fp(supplier),stage=install)
            self.assertEqual(tree_state(root),before)

            saved=driver.install_frozen_file(supplier,install/'safe/fixture.bin',
                        driver.fp(supplier),stage=install)
            self.assertTrue(driver.same(saved['installed'],driver.fp(supplier)))
            self.assertEqual(driver.install_frozen_file(supplier,
                install/'safe/fixture.bin',driver.fp(supplier),stage=install)['method'],
                'existing_identical')

    def test_I2_successful_normal_requires_exact_object_but_failed_steps_resume(self):
        # Exact AST identity prevents the source fragment drifting from the driver.
        def validator(path):
            tree=ast.parse(path.read_text())
            return next(n for n in tree.body if isinstance(n,ast.FunctionDef)
                        and n.name=='validated_receipt')
        self.assertEqual(ast.dump(validator(HERE/'receipt_reuse.py'),include_attributes=False),
                         ast.dump(validator(HERE/'Cell01Batch_verify.py'),include_attributes=False))
        with tempfile.TemporaryDirectory(prefix='p26-boundary-I2-') as name:
            root=Path(name).resolve()
            source=root/'source-fixture.txt'; source.write_bytes(b'frozen source bytes')
            obj=root/'object-fixture.bin'; original_object=b'accepted exact object'
            obj.write_bytes(original_object)
            audit=root/'audit-fixture.txt'; audit.write_bytes(b'owned audit fixture')
            lean=root/'fake-lean'; lean.write_bytes(b'never executed')
            checker=root/'fake-checker'; checker.write_bytes(b'never executed')
            supplier=root/'supplier.json'; supplier.write_text('{}')
            inputs=root/'inputs.json'; inputs.write_text('{}')
            installs=root/'installs.json'; installs.write_text('{}')
            attempt=root/'verification'/'prior'; folder=attempt/'Fixture'
            folder.mkdir(parents=True)
            log=folder/'normal.log'; log.write_text('')
            source_pin,obj_pin,audit_pin=map(driver.fp,[source,obj,audit])
            context={'runtime_context_sha256':'fixture-context',
                'supplier_manifest':driver.fp(supplier),'lean_version':'fixture-only',
                'mathlib_commit':'fixture-only','lean_binary':driver.fp(lean),
                'leanchecker_binary':driver.fp(checker),'LEAN_PATH':str(root),
                'cwd':str(root),'mathlib_package_object_roots':[],
                'required_mathlib_packages':[],
                'full_supplier_kernel_closed':True,'cloud_source_generation':False,
                'suppliers_recompiled':False}
            (attempt/'RUN.json').write_text(json.dumps(context))
            command={**context,'module':'Fixture','mode':'normal','source':source_pin,
                'object_before':None,'rss_limit_bytes':1024**3,
                'argv':[str(lean),'-j1','-M1024','-DmaxRecDepth=1000000',
                        '-DmaxHeartbeats=0','-o',str(obj),source.name]}
            command_path=folder/'normal-command.json'
            command_path.write_text(json.dumps(command))
            receipt={**command,'status':'succeeded','exit_code':0,'object':obj_pin,
                'command':driver.fp(command_path),'log':driver.fp(log),
                'input_fingerprints':driver.fp(inputs),
                'supplier_installation':driver.fp(installs),'printed_axioms':[]}
            receipt_path=folder/'normal-result.json'
            receipt_path.write_text(json.dumps(receipt))
            with mock.patch.object(driver.subprocess,'Popen',
                   side_effect=AssertionError('No proof command is allowed in this test')):
                accepted=driver.validated_receipt(receipt_path,'Fixture','normal',
                    source_pin,driver.fp(obj),audit_pin,context)
                self.assertEqual(accepted,receipt)

                obj.unlink()
                for use_context in [context,{**context,'runtime_context_sha256':'changed'}]:
                    with self.subTest(missing_object_context=use_context['runtime_context_sha256']):
                        with self.assertRaisesRegex(RuntimeError,'RESTORE_EXACT_ACCEPTED_OBJECT'):
                            driver.validated_receipt(receipt_path,'Fixture','normal',
                                source_pin,None,audit_pin,use_context)
                obj.write_bytes(b'changed or partial object')
                with self.assertRaisesRegex(RuntimeError,'RESTORE_EXACT_ACCEPTED_OBJECT'):
                    driver.validated_receipt(receipt_path,'Fixture','normal',
                        source_pin,driver.fp(obj),audit_pin,context)

                # Bad remaining evidence never turns a known normal success into a rebuild.
                log.unlink()
                with self.assertRaisesRegex(RuntimeError,'RESTORE_EXACT_ACCEPTED_OBJECT'):
                    driver.validated_receipt(receipt_path,'Fixture','normal',
                        source_pin,None,audit_pin,{**context,'runtime_context_sha256':'changed'})
                log.write_text('')
                obj.write_bytes(original_object)

                for mode in ['normal','kernel','owned']:
                    failed={**receipt,'status':'failed','exit_code':1,'mode':mode}
                    receipt_path.write_text(json.dumps(failed))
                    self.assertIsNone(driver.validated_receipt(receipt_path,'Fixture',mode,
                        source_pin,None if mode=='normal' else driver.fp(obj),audit_pin,context))
                receipt_path.write_text(json.dumps(receipt))
                self.assertEqual(driver.validated_receipt(receipt_path,'Fixture','normal',
                    source_pin,driver.fp(obj),audit_pin,context),receipt)
                self.assertEqual(list((root/'never-run').glob('*/normal-result.json')),[])

if __name__=='__main__':
    unittest.main(verbosity=2)
