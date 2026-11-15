"""GitHub-only metadata policy fixtures. Fake files never become proof receipts."""
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest

if os.environ.get('GITHUB_ACTIONS') != 'true':
    raise SystemExit('Never execute fixtures locally')

from cache_preexec_policy import enforce
from cache_runtime_setup import ANCHOR, insert_hook


class CacheProtectionCases(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory(prefix='cache-policy-fake-unit-')
        self.addCleanup(self.directory.cleanup);self.root=Path(self.directory.name)
        self.policy={'context':{'fake_unit_data':True},'project':str(self.root), 'deny_roots':[str(self.root/'goldbach')],
                     'deny_exact_paths':[str(self.root/'OldParent.lean')], 'denial_log':str(self.root/'denials.jsonl'),
                     'event_log':str(self.root/'events.jsonl'), 'metadata_cwds':[str(self.root)],
                     'qualification':str(self.root/'qualification.json'), 'cache_link_output':str(self.root/'cache'),
                     'caller_inputs':str(self.root/'caller-inputs.json'),
                     'cache_link_response':str(self.root/'cache.rsp'), 'admitted_commands':[]}
        source=self.root/'New031.lean';source.write_text('-- FAKE METADATA UNIT ONLY\n')
        self.policy['admitted_commands'].append({'tool':'lean','argv':['-t0','-j2','-M12288','-D','warningAsError=true',str(source)],
            'phase':'qualified-project','classification':'EXACT_ORIGINAL_CALLER_AUDIT','source':{'path':str(source)}})
        (self.root/'qualification.json').write_text(json.dumps({'binding':self.policy['context'],
            'status':'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY'}))
        (self.root/'caller-inputs.json').write_text(json.dumps({'binding':self.policy['context'],
            'qualification_sha256':hashlib.sha256((self.root/'qualification.json').read_bytes()).hexdigest(),
            'sources':{str(source):{'path':str(source),'bytes':source.stat().st_size,'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}}}))
        self.path=self.root/'policy.json';self.path.write_text(json.dumps(self.policy))
        self.sha=hashlib.sha256(self.path.read_bytes()).hexdigest()

    def call(self,argv,raw=None):enforce('lean',argv,self.root,self.path,self.sha,raw_argv=argv if raw is None else raw)

    def clang_case(self):
        # The policy row comes from the immutable historical protocol, while
        # the actual argv below is the literal shape in failed run43345599845.
        # Real filesystem links reproduce the original guard's include map.
        realroot=self.root/'official/leanprover--lean4---v4.33.0-rc1'
        shadow=self.root/'p0-ci-shadow-toolchain'
        (realroot/'include/clang').mkdir(parents=True);shadow.mkdir()
        (shadow/'include').symlink_to(realroot/'include',target_is_directory=True)
        self.policy['toolchain_roots']={'realroot':str(realroot),'shadow':str(shadow)}
        protocol=json.loads(Path(__file__).with_name('COMPILER_PROTOCOL.json').read_text())
        template=next(r for r in protocol['commands'] if r['tool']=='clang' and
                      r['argv'][3].endswith('/Cache/Cli.c'))
        replacements={'{project}':str(self.root),'{shadow}':str(shadow),'{realroot}':str(realroot)}
        def substitute(token):
            for old,new in replacements.items():token=token.replace(old,new)
            return token
        self.policy['admitted_commands'].append(dict(template,argv=[substitute(a) for a in template['argv']]))
        self.path.write_text(json.dumps(self.policy));self.sha=hashlib.sha256(self.path.read_bytes()).hexdigest()
        stem=str(self.root/'.lake/packages/mathlib/.lake/build/ir/Cache/Cli.c')
        argv=['-c','-o',stem+'.o.export',stem,'-I',str(shadow/'include'),
              '-fstack-clash-protection','-ffp-contract=off','-fdata-sections','-ffunction-sections',
              '-fPIC','-fvisibility=hidden','-Wno-unused-command-line-argument','--sysroot',str(shadow),
              '-nostdinc','-isystem',str(shadow/'include/clang'),'-O3','-DNDEBUG','-DLEAN_EXPORTING']
        return argv,realroot,shadow

    def call_clang(self,argv):enforce('clang',argv,self.root,self.path,self.sha,raw_argv=argv)

    def test_clang_bootstrap_exact_shadow_include_command_allowed(self):
        argv,realroot,shadow=self.clang_case()
        self.call_clang(argv)
        self.assertFalse((self.root/'denials.jsonl').exists())
        event=json.loads((self.root/'events.jsonl').read_text())
        self.assertEqual(event['classification'],'EXACT_PINNED_BOOTSTRAP_NATIVE')
        self.assertTrue(event['compiler_exec_permitted'])

    def test_clang_extra_or_changed_flag_denied(self):
        argv,realroot,shadow=self.clang_case()
        for variant in [argv+['-march=native'],[('-O2' if a=='-O3' else a) for a in argv]]:
            with self.assertRaises(RuntimeError):self.call_clang(variant)

    def test_clang_external_alias_to_same_include_denied(self):
        argv,realroot,shadow=self.clang_case()
        alias=self.root/'external-include';alias.symlink_to(realroot/'include',target_is_directory=True)
        argv[5]=str(alias)
        with self.assertRaises(RuntimeError):self.call_clang(argv)

    def test_clang_shadow_include_escape_denied(self):
        argv,realroot,shadow=self.clang_case()
        outside=self.root/'outside';(outside/'clang').mkdir(parents=True)
        (shadow/'include').unlink();(shadow/'include').symlink_to(outside,target_is_directory=True)
        with self.assertRaises(RuntimeError):self.call_clang(argv)

    def test_clang_nested_include_escape_denied(self):
        argv,realroot,shadow=self.clang_case()
        outside=self.root/'outside';outside.mkdir()
        (realroot/'include/clang').rmdir()
        (realroot/'include/clang').symlink_to(outside,target_is_directory=True)
        with self.assertRaises(RuntimeError):self.call_clang(argv)

    def test_clang_unregistered_source_or_output_denied(self):
        argv,realroot,shadow=self.clang_case()
        for index in [2,3]:
            variant=list(argv);variant[index]+='.unregistered'
            with self.assertRaises(RuntimeError):self.call_clang(variant)

    def test_reuse_only_denies_pinned_bootstrap_compile_and_link(self):
        argv,realroot,shadow=self.clang_case()
        self.policy['bootstrap_cache_reuse_only']=True
        self.path.write_text(json.dumps(self.policy));self.sha=hashlib.sha256(self.path.read_bytes()).hexdigest()
        with self.assertRaises(RuntimeError):self.call_clang(argv)
        with self.assertRaises(RuntimeError):self.call_clang(['-o',self.policy['cache_link_output'],
                                                            '@'+self.policy['cache_link_response']])

    def test_source_symlink_into_protected_cache_denied(self):
        protected=self.root/'goldbach/Protected.lean';protected.parent.mkdir();protected.write_text('-- FAKE UNIT\n')
        source=self.root/'New031.lean';source.unlink();source.symlink_to(protected)
        with self.assertRaises(RuntimeError):self.call(['-t0','-j2','-M12288','-D','warningAsError=true','New031.lean'])

    def test_native_source_denied_before_fake_exec(self):
        sentinel=self.root/'FAKE_EXEC_WAS_CALLED'
        def fake_program():
            self.call(['goldbach/MathlibNt/Fake.lean']);sentinel.touch()
        with self.assertRaises(RuntimeError):fake_program()
        self.assertFalse(sentinel.exists())

    def test_parent_denied_before_fake_exec(self):
        with self.assertRaises(RuntimeError):self.call(['OldParent.lean'])
        self.assertEqual(len((self.root/'denials.jsonl').read_text().splitlines()),1)

    def test_modern_IR_codegen_denied(self):
        with self.assertRaises(RuntimeError):self.call(['goldbach/.lake/build/lib/lean/Euler.ir'])

    def test_path_traversal_cannot_bypass(self):
        with self.assertRaises(RuntimeError):self.call(['other/../goldbach/A.lean'])

    def test_policy_mutation_rejected(self):
        self.path.write_text('{}')
        with self.assertRaises(RuntimeError):self.call(['AllowedNew.lean'])

    def test_new_project_source_allowed(self):
        self.call(['-t0','-j2','-M12288','-D','warningAsError=true','New031.lean'])
        self.assertFalse((self.root/'denials.jsonl').exists())
        self.assertEqual(json.loads((self.root/'events.jsonl').read_text())['classification'],'EXACT_ORIGINAL_CALLER_AUDIT')

    def test_metadata_prefix_probe_allowed(self):self.call(['-t0','-j2','-M12288','--print-prefix'],raw=['--print-prefix'])

    def test_metadata_raw_extra_resource_option_denied(self):
        with self.assertRaises(RuntimeError):self.call(['-t0','-j2','-M12288','--githash'],raw=['--threads','8','--githash'])

    def test_metadata_with_extra_source_is_denied(self):
        with self.assertRaises(RuntimeError):self.call(['-t0','-j2','-M12288','--print-prefix','New031.lean'])

    def test_unknown_stdin_and_response_are_denied(self):
        for argv in [['--stdin'],['@args'],['-oHidden.olean','New031.lean'],['--deps','New031.lean']]:
            with self.assertRaises(RuntimeError):self.call(argv)

    def test_unknown_tool_and_native_mode_are_denied(self):
        for tool in ['leanir','clang','leanc','llvm-ar']:
            with self.assertRaises(RuntimeError):enforce(tool,['New031.lean'],self.root,self.path,self.sha)

    def test_project_compile_before_qualification_denied(self):
        (self.root/'qualification.json').unlink()
        with self.assertRaises(RuntimeError):self.call(['-t0','-j2','-M12288','-D','warningAsError=true','New031.lean'])

    def test_admitted_audit_mutation_denied(self):
        (self.root/'New031.lean').write_text('-- CHANGED FAKE AUDIT\n')
        with self.assertRaises(RuntimeError):self.call(['-t0','-j2','-M12288','-D','warningAsError=true','New031.lean'])

    def test_long_option_cannot_hide_protected_path(self):
        with self.assertRaises(RuntimeError):self.call(['--setup=goldbach/.lake/build/ir/A.setup.json'])

    def test_hook_precedes_original_log_and_exec(self):
        fake=ANCHOR+"\n# FAKE_UNIT_ONLY\nwith open(C['log'], 'a') as log:\n  pass\nos.execv(cmd[0], cmd)\n"
        extended,hook=insert_hook(fake,self.path,self.sha)
        self.assertLess(extended.index('_cache_policy.enforce'),extended.index("with open(C['log']"))
        self.assertLess(extended.index('_cache_policy.enforce'),extended.index('os.execv'))
        self.assertEqual(extended.replace(hook,''),fake)


    def direct_case(self):
        source=self.root/'New031.lean'
        setup=self.root/'new.setup.json';setup.write_text('{}')
        dependency=self.root/'dependency.olean';dependency.write_bytes(b'FAKE METADATA ONLY')
        def rec(path):
            raw=path.read_bytes()
            return dict(path=str(path),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        command=self.policy['admitted_commands'][0]
        receipt=self.root/'direct-inputs.json'
        receipt.write_text(json.dumps(dict(binding=self.policy['context'],source=rec(source),
            normalized_argv=command['argv'],files=[rec(setup),rec(dependency)])))
        command['input_binding']=str(receipt)
        self.path.write_text(json.dumps(self.policy));self.sha=hashlib.sha256(self.path.read_bytes()).hexdigest()
        return command['argv'],receipt,setup,dependency

    def test_direct_exact_setup_and_import_inputs_admitted(self):
        argv,receipt,setup,dependency=self.direct_case();self.call(argv)

    def test_direct_setup_mutation_denied_before_exec(self):
        argv,receipt,setup,dependency=self.direct_case();setup.write_text('{"changed":true}')
        with self.assertRaises(RuntimeError):self.call(argv)

    def test_direct_import_mutation_denied_before_exec(self):
        argv,receipt,setup,dependency=self.direct_case();dependency.write_bytes(b'CHANGED')
        with self.assertRaises(RuntimeError):self.call(argv)

    def test_direct_missing_import_denied_before_exec(self):
        argv,receipt,setup,dependency=self.direct_case();dependency.unlink()
        with self.assertRaises(RuntimeError):self.call(argv)

    def test_direct_receipt_other_run_denied(self):
        argv,receipt,setup,dependency=self.direct_case();value=json.loads(receipt.read_text())
        value['binding']={};receipt.write_text(json.dumps(value))
        with self.assertRaises(RuntimeError):self.call(argv)

    def test_direct_receipt_other_argv_denied(self):
        argv,receipt,setup,dependency=self.direct_case();value=json.loads(receipt.read_text())
        value['normalized_argv']=['--run'];receipt.write_text(json.dumps(value))
        with self.assertRaises(RuntimeError):self.call(argv)

    def test_header_nested_comments_meta_all_and_prelude(self):
        from weil_inputs import header
        value=header('/- outer /- nested -/ -/\nmodule\nprelude\npublic meta import all Lean.Util.FoldConsts\npublic section\ndef x := 1')
        self.assertTrue(value['is_module']);self.assertTrue(value['prelude'])
        self.assertEqual(value['imports'],['Lean.Util.FoldConsts'])
        self.assertEqual(value['explicit_imports'],[dict(module='Lean.Util.FoldConsts',import_all=True,is_meta=True,is_exported=True)])

    def test_header_body_string_does_not_invent_import(self):
        from weil_inputs import header
        value=header('module\nimport Mathlib.Data.Nat.Sqrt\ndef message := "import Evil.Hidden /-"')
        self.assertEqual(value['imports'],['Init','Mathlib.Data.Nat.Sqrt'])

    def test_header_legacy_default_init_and_visibility(self):
        from weil_inputs import header
        value=header('import Lean.Util.FoldConsts\nnamespace Test')
        self.assertFalse(value['is_module']);self.assertEqual(value['imports'],['Init','Lean.Util.FoldConsts'])
        self.assertTrue(value['explicit_imports'][0]['is_exported'])

    def test_header_unknown_import_identifier_holds(self):
        from weil_inputs import header
        with self.assertRaises(ValueError):header('module\nimport «Unbound Module»')

    def test_header_unclosed_comment_holds(self):
        from weil_inputs import header
        with self.assertRaises(ValueError):header('/- unclosed\nmodule\nimport Init')


def main():
    from coherent_cache import bind_inputs, HERE, read, write
    binding=bind_inputs(os.environ['CACHE_SCOPE']);logs=Path(os.environ['LOGS'])
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(CacheProtectionCases)
    from r3_negative_fixtures import R3ProtectionCases
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(R3ProtectionCases))
    from r4_negative_fixtures import R4ProtectionCases
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(R4ProtectionCases))
    from r4_bound_negative_fixtures import R4BoundInputCases
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(R4BoundInputCases))
    from r4_donor_ledger_fixtures import R4DonorLedgerCases
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(R4DonorLedgerCases))
    names=[case._testMethodName for case in suite]
    expected=read(HERE/'CACHE_FIXTURE_CONTRACT.json')['test_names']
    if names!=expected:raise ValueError('Fixture census changed')
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    value={'binding':binding,'test_names':names,'tests_run':result.testsRun,'errors':len(result.errors),
           'failures':len(result.failures),'skipped':len(result.skipped),'successful':result.wasSuccessful(),
           'fake_metadata_is_not_a_proof_or_cache_hit':True}
    from coherent_cache import sha
    value['r3_gate_sources']={name:sha(HERE/name) for name in [
        'r3_negative_fixtures.py','qualified_algebra.py','weil_cache.py','weil_retention.py','cache_preexec_policy.py']}
    value['r4_gate_sources']={name:sha(HERE/name) for name in [
        'qualified_direct.py','r4_negative_fixtures.py','weil_proof.py','weil_scope.py','carrier_originals.py','r4_bound_negative_fixtures.py','r4_donor_ledger_fixtures.py']}
    write(logs/'CACHE_FIXTURE_RESULT.json',value)
    return 0 if result.wasSuccessful() else 1


if __name__=='__main__':raise SystemExit(main())
