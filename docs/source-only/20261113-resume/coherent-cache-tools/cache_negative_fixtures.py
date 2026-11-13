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


def main():
    from coherent_cache import bind_inputs, HERE, read, write
    binding=bind_inputs(os.environ['CACHE_SCOPE']);logs=Path(os.environ['LOGS'])
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(CacheProtectionCases)
    names=[case._testMethodName for case in suite]
    expected=read(HERE/'CACHE_FIXTURE_CONTRACT.json')['test_names']
    if names!=expected:raise ValueError('Fixture census changed')
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    value={'binding':binding,'test_names':names,'tests_run':result.testsRun,'errors':len(result.errors),
           'failures':len(result.failures),'skipped':len(result.skipped),'successful':result.wasSuccessful(),
           'fake_metadata_is_not_a_proof_or_cache_hit':True}
    write(logs/'CACHE_FIXTURE_RESULT.json',value)
    return 0 if result.wasSuccessful() else 1


if __name__=='__main__':raise SystemExit(main())
