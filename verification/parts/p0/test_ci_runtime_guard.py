#!/usr/bin/env python3
"""Deterministic static/stub tests. Never runs installed Lean, Lake or checker."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


guard = load('ci_guard', HERE / 'ci_runtime_guard.py')
publication = load('ci_publication', HERE / 'queue/check_publication.py')

# This Python fake models fixed Lake's app-path detection and environment order.
# For a symlink it sees realbin first; for the byte-identical copy, shadow first.
FAKE_TOOL = r'''#!/usr/bin/env python3
import fcntl, json, os, pathlib, subprocess, sys, time
name = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
if name == 'lake':
    home = pathlib.Path(__file__).resolve().parent.parent
    shadow = pathlib.Path(os.environ['LEAN_SYSROOT'])
    env = os.environ.copy()
    env.update(PATH=str(home/'bin')+':'+str(shadow/'bin')+':'+env['PATH'],
               LAKE=str(home/'bin/lake'), LAKE_HOME=str(home),
               LEAN=str(shadow/'bin/lean'), LEAN_AR=str(shadow/'bin/llvm-ar'))
    if args[0] == 'env':
        sys.exit(subprocess.run(args[1:], env=env).returncode)
    if args[0] == 'build':
        subprocess.run([str(shadow/'bin/lean'), '-j8', '-M9000', 'Fake.lean'], env=env, check=True)
        subprocess.run([str(shadow/'bin/clang'), '-O3', '-c', 'Fake.c'], env=env, check=True)
        if pathlib.Path.cwd().name == 'axiom-audit':
            p = pathlib.Path('.lake/build/bin/axiom-audit'); p.parent.mkdir(parents=True)
            p.write_text('#!/bin/sh\nexit 0\n'); p.chmod(0o755)
        sys.exit(0)
    raise RuntimeError('unexpected fake lake command')
if name == 'lean' and '--print-prefix' in args:
    print(os.environ['LEAN_SYSROOT']); sys.exit(0)
if '--nested' in args:
    args.remove('--nested')
    # Native descendant receives HELD even if subprocess closes inherited FDs.
    sys.exit(subprocess.run([os.environ['LEAN_SYSROOT']+'/bin/clang','-O3'], close_fds=True).returncode)
with open(os.environ['FAKE_EVENTS'], 'a') as out:
    fcntl.flock(out, fcntl.LOCK_EX)
    out.write(json.dumps({'name':name,'args':args,'threads':os.environ.get('LEAN_NUM_THREADS')})+'\n')
# Separate nonblocking assertion lock proves independently spawned wrappers serialize.
with open(os.environ['FAKE_ACTIVE'], 'a') as active:
    fcntl.flock(active, fcntl.LOCK_EX | fcntl.LOCK_NB)
    time.sleep(0.025)
if '--fail' in args:
    sys.exit(23)
'''


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='p0-ci-stub-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'project'; self.root.mkdir()
        self.runner = self.base / 'runner'; self.runner.mkdir()
        self.realbin = self.base / 'fixed-pin' / 'bin'; self.realbin.mkdir(parents=True)
        (self.realbin.parent / 'lib' / 'lean').mkdir(parents=True)
        for name in (*guard.TOOLS, 'lake', 'leanchecker'):
            p = self.realbin / name; p.write_text(FAKE_TOOL); p.chmod(0o755)
        (self.root / 'lean-toolchain').write_text(guard.PIN + '\n')
        for name in ('lakefile.toml', 'lake-manifest.json'):
            (self.root / name).write_text('{}\n')
        env = {k: v for k, v in os.environ.items() if k not in guard.AMBIGUOUS_ENV}
        env.update(LEAN_NUM_THREADS='2', RUNNER_TEMP=str(self.runner),
                   FAKE_EVENTS=str(self.base / 'events.jsonl'), FAKE_ACTIVE=str(self.base / 'active.lock'))
        self.env = patch.dict(os.environ, env, clear=True); self.env.start(); self.addCleanup(self.env.stop)
        self.state = guard.prepare(self.root, self.runner, self.runner / 'evidence',
                                   self.realbin, self.base / 'fake-action', verify_action=False)
        os.environ.update(self.state['environment'])
        os.environ['PATH'] = self.state['shadow'] + '/bin:' + os.environ['PATH']
        self.state_path = Path(os.environ['P0_CI_GUARD_STATE'])

    def run_tool(self, name, *args, check=True):
        return subprocess.run([self.state['shadow']+'/bin/'+name, *args], cwd=self.root,
                              text=True, capture_output=True, check=check, timeout=10)

    def records(self):
        return [json.loads(x) for x in Path(self.state['log']).read_text().splitlines()]

    def test_resource_overrides_normalized_and_warning_policy_preserved(self):
        self.run_tool('lean', '-t', '99', '-j8', '-M9000', '--threads=16',
                      '--trust', '5', '--memory=9999', '-o', 'x.olean', 'X.lean')
        cmd = self.records()[-1]['command']
        self.assertEqual(cmd[1:], ['-t0','-j2','-M4096','-o','x.olean','X.lean'])
        self.assertNotIn('-DwarningAsError=true', cmd)
        self.run_tool('lean', '-DwarningAsError=true', 'Audit.lean')
        self.assertIn('warningAsError=true', self.records()[-1]['command'])
        guard.audit(self.state_path, require_source=True)

    def test_trust_clusters_and_timeout_are_distinct(self):
        self.run_tool('lean', '-qt5', '-j', '9', '-M8192', '--trust=9',
                      '--timeout=30', '-T40', '-DmaxRecDepth=1000', '-o', '-j9.olean', 'X.lean')
        self.assertEqual(self.records()[-1]['command'][1:],
                         ['-t0','-j2','-M4096','-q','--timeout=30','-T','40',
                          '-D','maxRecDepth=1000','-o','-j9.olean','X.lean'])

    def test_malformed_or_abbreviated_resources_fail_closed(self):
        for args in [('-j',), ('-M', 'X.lean'), ('--thre=8',), ('-tbad',), ('--tru=1',), ('-M=9999',)]:
            self.assertNotEqual(self.run_tool('lean', *args, check=False).returncode, 0)
        self.assertEqual(self.records(), [])

    def test_native_flags_unchanged(self):
        for name in guard.TOOLS[1:]:
            self.run_tool(name, '-O3', '-MMD', '-j8', '-t99', 'native.c')
            self.assertEqual(self.records()[-1]['command'][1:], ['-O3','-MMD','-j8','-t99','native.c'])

    def test_all_compilers_share_one_slot(self):
        procs = [subprocess.Popen([self.state['shadow']+'/bin/'+name, 'Fake.lean' if name=='lean' else 'Fake.c'],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE) for name in guard.TOOLS * 2]
        for proc in procs:
            out, err = proc.communicate(timeout=10)
            self.assertEqual(proc.returncode, 0, err.decode())
        self.assertEqual(len(self.records()), 10)

    def test_nested_native_child_shares_live_ancestor_slot(self):
        self.run_tool('leanc', '--nested', 'Fake.c')
        leanc, clang = self.records()
        self.assertEqual(leanc['slot_owner'], clang['slot_owner'])
        self.assertEqual(clang['tool'], 'clang')

    def test_nested_source_or_unreviewed_native_chain_fails(self):
        for name in ('lean', 'leanir', 'clang', 'llvm-ar'):
            self.assertNotEqual(self.run_tool(name,'--nested','Fake.lean',check=False).returncode,0)

    def test_run_mode_is_explicitly_out_of_scope(self):
        for option in ('--run','--ru','--run=Program.lean','-r','-qr'):
            self.assertNotEqual(self.run_tool('lean',option,'Program.lean',check=False).returncode,0)

    def test_pin_resolution_uses_supported_elan_environment(self):
        calls=[]
        def fake_capture(*command,env=None):
            self.assertEqual(command[:2],('elan','which'))
            self.assertEqual(len(command),3)
            if env is not None:self.assertEqual(env['ELAN_TOOLCHAIN'],guard.PIN)
            calls.append((command,env))
            return str(self.realbin/command[-1])
        with patch.object(guard,'capture',side_effect=fake_capture):
            self.assertEqual(guard.resolve_pin(),self.realbin)
        self.assertEqual(len(calls),6)
        with patch.object(guard,'capture',side_effect=lambda *c,env=None:str((self.realbin if env else self.base/'other/bin')/c[-1])):
            with self.assertRaisesRegex(RuntimeError,'not the fixed pin'):guard.resolve_pin()

    def test_forged_slot_owner_fails(self):
        with patch.dict(os.environ, P0_COMPILER_SLOT_HELD='1', P0_COMPILER_SLOT_FD='999999'):
            self.assertNotEqual(self.run_tool('lean','X.lean',check=False).returncode,0)
        self.assertEqual(self.records(), [])

    def test_native_checker_unmodified(self):
        self.run_tool('leanchecker', '--verbose', 'ImbalancedChen')
        events = [json.loads(x) for x in Path(os.environ['FAKE_EVENTS']).read_text().splitlines()]
        self.assertEqual(events[-1], {'name':'leanchecker','args':['--verbose','ImbalancedChen'],'threads':'2'})
        self.assertEqual(self.records(), [])

    def test_effective_lake_child_environment_in_both_directories(self):
        result = guard.audit(self.state_path, probe=True)
        self.assertTrue(result['probe'])
        self.assertTrue(self.records())

    def test_symlink_lake_would_bypass_and_is_rejected(self):
        lake = Path(self.state['shadow'])/'bin/lake'
        lake.unlink(); lake.symlink_to(self.realbin/'lake')
        # Same content hash is insufficient: fixed Lake changes PATH by appPath.
        with self.assertRaisesRegex(RuntimeError, 'byte-identical copy'):
            guard.audit(self.state_path, probe=True)
        probe = self.run_tool('lake','env',sys.executable,str(HERE/'ci_runtime_guard.py'),
                              'probe','--state',str(self.state_path),check=False)
        self.assertNotEqual(probe.returncode,0)
        self.assertIn('PATH bypasses wrapper',probe.stderr)

    def test_path_environment_and_runtime_tampering_fail_closed(self):
        for key, value in [('LEAN_SYSROOT',str(self.realbin.parent)), ('LEAN',str(self.realbin/'lean')),
                           ('LEAN_CC','cc'), ('LEAN_NUM_THREADS','8')]:
            with patch.dict(os.environ, {key:value}):
                with self.assertRaises(RuntimeError): guard.audit(self.state_path)
                self.assertNotEqual(self.run_tool('lean','X.lean',check=False).returncode,0)
        with patch.dict(os.environ, PATH=str(self.realbin)+':'+os.environ['PATH']):
            with self.assertRaisesRegex(RuntimeError,'PATH bypasses'): guard.audit(self.state_path)
        (Path(self.state['shadow'])/'bin/lean').write_text('# changed\n')
        with self.assertRaisesRegex(RuntimeError,'Changed pinned runtime'): guard.audit(self.state_path)

    def test_real_runtime_change_fails(self):
        (self.realbin/'clang').write_text('# changed\n')
        with self.assertRaisesRegex(RuntimeError,'Changed pinned runtime'): guard.audit(self.state_path)

    def test_command_log_later_resource_overrides_fail_audit(self):
        self.run_tool('lean','X.lean')
        original=self.records()[0]
        for flag in ('--trust=1','-j8','-M8192'):
            record={**original,'command':original['command']+[flag]}
            Path(self.state['log']).write_text(json.dumps(record)+'\n')
            with self.assertRaisesRegex(RuntimeError,'differs from normalized input'):
                guard.audit(self.state_path)

    def test_no_recorded_source_fails_final_gate(self):
        with self.assertRaisesRegex(RuntimeError,'No guarded Lean source'): guard.audit(self.state_path,require_source=True)

    def test_compiler_failure_is_preserved(self):
        self.assertEqual(self.run_tool('lean','--fail','X.lean',check=False).returncode,23)

    def test_existing_environment_or_root_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'Ambiguous existing runtime environment'):
            guard.prepare(self.root,self.runner,self.runner/'other',self.realbin,self.base,False)
        clean={k:v for k,v in os.environ.items() if k not in guard.AMBIGUOUS_ENV}
        with patch.dict(os.environ,clean,clear=True):
            with self.assertRaisesRegex(RuntimeError,'existing shadow'):
                guard.prepare(self.root,self.runner,self.runner/'other',self.realbin,self.base,False)

    def test_evidence_does_not_contain_shadow_or_symlinks(self):
        evidence = self.state_path.parent
        self.assertFalse(any(p.is_symlink() for p in evidence.rglob('*')))
        self.assertEqual(guard.sha(self.realbin/'lake'), guard.sha(Path(self.state['shadow'])/'bin/lake'))
        for name in guard.TOOLS:
            self.assertEqual(guard.sha(evidence/(name+'-wrapper.py')), guard.sha(Path(self.state['shadow'])/'bin'/name))

    @unittest.skipUnless(os.environ.get('P0_TEST_LEAN_ACTION_DIR'),'optional exact pinned action fixture not supplied')
    def test_exact_upstream_build_and_axiom_audit_scripts(self):
        action = Path(os.environ['P0_TEST_LEAN_ACTION_DIR'])
        for name, expected in guard.ACTION_SHA256.items():
            self.assertEqual(guard.sha(action/'scripts'/name), expected)
        os.environ.update(BUILD_ARGS='', GITHUB_OUTPUT=str(self.base/'github-output'),
                          AXIOM_AUDIT_ROOT='ImbalancedChen', AXIOM_AUDIT_ALLOW='propext,Classical.choice,Quot.sound')
        # Stub only the pinned audit's network git clone and SHA query.
        fakebin=self.base/'fakebin';fakebin.mkdir()
        git=fakebin/'git';git.write_text('''#!/usr/bin/env python3
import pathlib,sys
if sys.argv[1]=='clone':
 p=pathlib.Path(sys.argv[-1]);p.mkdir();(p/'lakefile.toml').write_text('name="axiom-audit"\\n')
elif sys.argv[1]=='-C' and sys.argv[3:]==['rev-parse','HEAD']:
 print('46024e005996495c65ef609368e11ab39c4222e3')
else: raise RuntimeError('unexpected git stub command')
''');git.chmod(0o755)
        os.environ['PATH']=self.state['shadow']+'/bin:'+str(fakebin)+':'+os.environ['PATH']
        for name in ('lake_build.sh','run_axiom_audit.sh'):
            proc=subprocess.run(['bash',str(action/'scripts'/name)],cwd=self.root,capture_output=True,text=True,timeout=15)
            self.assertEqual(proc.returncode,0,proc.stdout+proc.stderr)
        sources=[r for r in self.records() if r['tool']=='lean']
        self.assertEqual(len(sources),3)  # full build, audit rebuild, external audit-tool build
        self.assertTrue(any('/axiom-audit' in r['cwd'] for r in sources))
        guard.audit(self.state_path,require_source=True)


def inline_admission(workflow_name):
    import yaml
    workflow=yaml.load((ROOT/'.github/workflows'/workflow_name).read_text(),Loader=yaml.BaseLoader)
    block=workflow['jobs']['pr-admission']['steps'][1]['run']
    code=block.split("python3 -I - <<'PYADMISSION'\n",1)[1].split('\nPYADMISSION',1)[0]
    return block,code


class PRSynchronizeAdmissionTests(unittest.TestCase):
    def setUp(self):
        import ast
        import re
        _,code=inline_admission('lean.yml')
        self.assertEqual(code,inline_admission('variable-envelope.yml')[1])
        # Execute only the exact workflow function definition. No repository
        # helper or real Git/Lean/toolchain process is run by these predicates.
        function=next(node for node in ast.parse(code).body if isinstance(node,ast.FunctionDef) and node.name=='pr_dispatch_decision')
        namespace={'re':re,'subprocess':subprocess}
        exec(compile(ast.Module(body=[function],type_ignores=[]),'<workflow-admission>','exec'),namespace)
        self.decide=namespace['pr_dispatch_decision']
        self.before,self.after,self.other='b'*40,'a'*40,'c'*40
        self.event={'action':'synchronize','before':self.before,'after':self.after,'repository':{'id':7},
                    'pull_request':{'head':{'ref':'codex/chen-parts-integration','sha':self.after,'repo':{'id':7}}}}

    def fake_git(self,paths=None,checked_out=None,parents=None):
        paths=paths if paths is not None else ['automation/root-dispatch.json']
        replies={('rev-parse','HEAD'):((checked_out or self.after)+'\n').encode(),
                 ('rev-list','--parents','-n','1','HEAD'):(' '.join(parents or [self.after,self.before])+'\n').encode(),
                 ('diff','--no-renames','--name-only','-z',self.before,self.after):('\0'.join(paths)+'\0').encode()}
        return lambda *args:replies[args]

    def test_only_exact_single_dispatch_synchronize_skips(self):
        for path in ('automation/dispatch.json','automation/root-dispatch.json'):
            result=self.decide('pull_request',self.event,self.fake_git([path]))
            self.assertTrue(result['skip_heavy'])
            self.assertEqual(result['status'],'SKIP_DUPLICATE_DISPATCH_ONLY')
            self.assertEqual(result['changed_paths'],[path])
        # Any older source/config changes in the PR's three-dot diff are
        # irrelevant: only the verified before -> after delta is inspected.

    def test_dispatch_and_pr_heavy_event_matrix(self):
        import yaml
        read=lambda name: yaml.load((ROOT/'.github/workflows'/name).read_text(),Loader=yaml.BaseLoader)
        core,ve,caller,finite=map(read,('lean.yml','variable-envelope.yml','p0-root-dispatch.yml','p0-queue.yml'))
        self.assertEqual(caller['on']['push']['paths'],['automation/root-dispatch.json'])
        self.assertEqual(finite['on']['push']['paths'],['automation/dispatch.json'])
        for workflow in (core,ve):
            self.assertEqual(workflow['on']['push']['branches-ignore'],['codex/chen-parts-integration'])
        def heavy_events(paths):
            decision=self.decide('pull_request',self.event,self.fake_git(paths))
            jobs=set() if decision['skip_heavy'] else {'core-pr','ve-pr'}
            # The caller additionally requires its strict one-commit admission.
            if paths==['automation/root-dispatch.json']:jobs.add('root-caller')
            if 'automation/dispatch.json' in paths:jobs.add('finite')
            return jobs
        self.assertEqual(heavy_events(['automation/root-dispatch.json']),{'root-caller'})
        self.assertEqual(heavy_events(['automation/dispatch.json']),{'finite'})
        for dispatch in ('automation/root-dispatch.json','automation/dispatch.json'):
            self.assertTrue({'core-pr','ve-pr'}<=heavy_events(['ImbalancedChen.lean',dispatch]))
        for path in ('.github/workflows/lean.yml','verification/parts/p0/ci_runtime_guard.py',
                     'automation/contracts/ownership.json','automation/locks/heavy.json'):
            self.assertEqual(heavy_events([path]),{'core-pr','ve-pr'})

    def test_other_events_missing_metadata_and_wrong_head_run_heavy(self):
        cases=[('push',self.event),('workflow_dispatch',self.event),('workflow_call',self.event)]
        for action in ('opened','reopened','edited','closed','ready_for_review'):
            cases.append(('pull_request',{**self.event,'action':action}))
        for key in ('before','after','pull_request'):
            cases.append(('pull_request',{k:v for k,v in self.event.items() if k!=key}))
        cases.extend([('pull_request',{**self.event,'before':'invalid'}),
                      ('pull_request',{**self.event,'pull_request':{'head':{'ref':'other','sha':self.after}}}),
                      ('pull_request',{**self.event,'pull_request':{'head':{'ref':'codex/chen-parts-integration','sha':self.other}}}),
                      ('pull_request',None)])
        for event_name,event in cases:
            result=self.decide(event_name,event,self.fake_git())
            self.assertFalse(result['skip_heavy'],repr(event))
            self.assertEqual(result['status'],'RUN_ORIGINAL_HEAVY_GATES')

    def test_fork_or_missing_repository_identity_never_skips(self):
        for head_id in (8,None,0,True,'7'):
            event=json.loads(json.dumps(self.event))
            event['pull_request']['head']['repo']={'id':head_id}
            self.assertFalse(self.decide('pull_request',event,self.fake_git())['skip_heavy'])
        for removal in ('repository','head-repo','repository-id'):
            event=json.loads(json.dumps(self.event))
            if removal=='repository':del event['repository']
            elif removal=='head-repo':del event['pull_request']['head']['repo']
            else:del event['repository']['id']
            self.assertFalse(self.decide('pull_request',event,self.fake_git())['skip_heavy'])

    def test_source_config_ownership_and_mixed_deltas_run_heavy(self):
        for path in ['ImbalancedChen.lean','.github/workflows/lean.yml','verification/parts/p0/ci_runtime_guard.py',
                     'automation/contracts/ownership.json','automation/locks/heavy.json','automation/control.json']:
            for paths in ([path],[path,'automation/root-dispatch.json'],[path,'automation/dispatch.json']):
                self.assertFalse(self.decide('pull_request',self.event,self.fake_git(paths))['skip_heavy'])
        for paths in [[],['automation/root-dispatch.json','automation/dispatch.json'],
                      ['automation/root-dispatch.json']*2,['automation/root-dispatch.json.bak']]:
            self.assertFalse(self.decide('pull_request',self.event,self.fake_git(paths))['skip_heavy'])

    def test_exact_inline_shell_never_executes_pr_head_helper(self):
        with tempfile.TemporaryDirectory(prefix='p0-pr-inline-stub-') as directory:
            base=Path(directory);fakebin=base/'bin';fakebin.mkdir()
            helper=base/'verification/parts/p0/ci_runtime_guard.py';helper.parent.mkdir(parents=True)
            helper.write_text("raise RuntimeError('PR head helper must not execute during admission')\n")
            for name in ('json.py','subprocess.py'):
                (base/name).write_text("raise RuntimeError('CWD stdlib shadow must not import during admission')\n")
            git=fakebin/'git'
            git.write_text('''#!/usr/bin/env python3
import json,os,sys
if os.environ.get('FAKE_GIT_ERROR')=='true':sys.exit(128)
v=json.loads(os.environ['FAKE_GIT_STATE']);a=sys.argv[1:]
if a==['rev-parse','HEAD']:print(v['head'])
elif a==['rev-list','--parents','-n','1','HEAD']:print(v['head']+' '+v['before'])
elif a[:4]==['diff','--no-renames','--name-only','-z']:sys.stdout.write('\\0'.join(v['paths'])+'\\0')
else:raise RuntimeError('unexpected fake git command')
''');git.chmod(0o755)
            event_path=base/'event.json';output=base/'output';summary=base/'summary'
            cases=[(['automation/root-dispatch.json'],'success',False,True),
                   (['automation/dispatch.json'],'success',False,True),
                   (['verification/parts/p0/ci_runtime_guard.py','automation/root-dispatch.json'],'success',False,False),
                   (['automation/root-dispatch.json'],'failure',False,False),
                   (['automation/root-dispatch.json'],'skipped',False,False),
                   (['automation/root-dispatch.json'],'success',True,False)]
            for workflow_name in ('lean.yml','variable-envelope.yml'):
                block,_=inline_admission(workflow_name)
                self.assertNotIn('python3 verification/',block)
                for paths,checkout,git_error,skip in cases:
                    event_path.write_text(json.dumps(self.event));output.write_text('');summary.write_text('')
                    env=dict(os.environ,PATH=str(fakebin)+':'+os.environ['PATH'],CHECKOUT_OUTCOME=checkout,
                             GITHUB_EVENT_NAME='pull_request',GITHUB_EVENT_PATH=str(event_path),
                             GITHUB_OUTPUT=str(output),GITHUB_STEP_SUMMARY=str(summary),FAKE_GIT_ERROR=str(git_error).lower(),
                             FAKE_GIT_STATE=json.dumps({'head':self.after,'before':self.before,'paths':paths}))
                    result=subprocess.run(['bash','-e','-o','pipefail','-c',block],cwd=base,env=env,
                                          text=True,capture_output=True,timeout=10)
                    self.assertEqual(result.returncode,0,result.stdout+result.stderr)
                    self.assertEqual(output.read_text(),'skip-heavy='+str(skip).lower()+'\n')
                    if skip:self.assertIn('not proof acceptance',summary.read_text())

    def test_checkout_git_multicommit_merge_and_incomplete_evidence_run_heavy(self):
        for git in [self.fake_git(checked_out=self.other),
                    self.fake_git(parents=[self.after,self.other]),
                    self.fake_git(parents=[self.after,self.before,self.other]),
                    self.fake_git(parents=[self.after]),
                    lambda *args: (_ for _ in ()).throw(subprocess.CalledProcessError(128,['git'])),
                    lambda *args:b'not a complete result']:
            self.assertFalse(self.decide('pull_request',self.event,git)['skip_heavy'])


class PublicationTests(unittest.TestCase):
    def test_only_exact_dispatches_can_trigger(self):
        for path in publication.TRIGGERS:
            self.assertFalse(publication.check('Run verification',[path])['skip_ci'])

    def test_negative_triggers(self):
        invalid=[[],['automation/other.json'],['automation/root-dispatch.json.bak'],
                 ['automation/sub/root-dispatch.json'],['.github/workflows/lean.yml'],
                 ['ImbalancedChen.lean'],['automation/root-dispatch.json','automation/dispatch.json'],
                 ['automation/root-dispatch.json','ImbalancedChen.lean'],
                 ['automation/root-dispatch.json','.github/workflows/lean.yml'],
                 ['automation/root-dispatch.json','automation/parts/p0/status.json'],
                 ['automation/root-dispatch.json']*2]
        for paths in invalid:
            with self.assertRaises(ValueError,msg=repr(paths)):publication.check('Run verification',paths)

    def test_skip_ci_does_not_allow_mixed_dispatch(self):
        self.assertTrue(publication.check('[SKIP CI] update source',['ImbalancedChen.lean'])['skip_ci'])
        for paths in [['automation/root-dispatch.json','ImbalancedChen.lean'],
                      ['automation/root-dispatch.json','automation/dispatch.json']]:
            with self.assertRaises(ValueError):publication.check('[skip ci]',paths)


class WorkflowStaticTests(unittest.TestCase):
    def test_server_admission_rejects_mixed_merge_multicommit_and_wrong_head(self):
        import yaml
        caller=yaml.load((ROOT/'.github/workflows/p0-root-dispatch.yml').read_text(),Loader=yaml.BaseLoader)
        block=caller['jobs']['admission']['steps'][1]['run']
        code=block.split("python3 -I - <<'PY'\n",1)[1].rsplit('PY',1)[0]
        with tempfile.TemporaryDirectory(prefix='p0-dispatch-stub-') as directory:
            base=Path(directory);fakebin=base/'bin';fakebin.mkdir()
            script=fakebin/'git'
            script.write_text('''#!/usr/bin/env python3
import json,os,sys
v=json.loads(os.environ['FAKE_GIT_STATE']);a=sys.argv[1:]
if a==['rev-parse','HEAD']: print(v['checked_out'])
elif a==['rev-list','--parents','-n','1','HEAD']: print(v['parents'])
elif a[:4]==['diff','--no-renames','--name-only','-z']: sys.stdout.write('\\0'.join(v['paths'])+'\\0')
elif a[:3]==['show','-s','--format=%B']: print('Run full root verification')
else: raise RuntimeError('unexpected git stub command')
''');script.chmod(0o755)
            head,before,other='a'*40,'b'*40,'c'*40
            good={'checked_out':head,'parents':head+' '+before,'paths':['automation/root-dispatch.json']}
            cases=[(good,True),({**good,'paths':['ImbalancedChen.lean','automation/root-dispatch.json']},False),
                   ({**good,'paths':['automation/dispatch.json','automation/root-dispatch.json']},False),
                   ({**good,'parents':head+' '+before+' '+other},False),
                   ({**good,'parents':head+' '+other},False),({**good,'checked_out':other},False),
                   ({**good,'paths':['old-source.lean','automation/root-dispatch.json']},False)]
            for case,success in cases:
                env=dict(os.environ,PATH=str(fakebin)+':'+os.environ['PATH'],EXPECTED_HEAD=head,
                         EXPECTED_BEFORE=before,RUNNER_TEMP=str(base),FAKE_GIT_STATE=json.dumps(case))
                result=subprocess.run([sys.executable,'-I','-c',code],cwd=ROOT,env=env,text=True,capture_output=True,timeout=10)
                self.assertEqual(result.returncode==0,success,result.stdout+result.stderr)

    def test_heavy_dependency_admission_failure_is_not_a_skip(self):
        # Mirrors the exact asserted GitHub expression: explicit !cancelled()
        # overrides the default needs-success guard, with unknown evidence run.
        for result in ('success','failure','skipped','cancelled',''):
            for output in ('true','false','',None,'unexpected'):
                runs=(result!='success' or output!='true')
                self.assertEqual(runs,not (result=='success' and output=='true'))
        import yaml
        for filename,job in [('lean.yml','lean'),('variable-envelope.yml','variable-envelope')]:
            workflow=yaml.load((ROOT/'.github/workflows'/filename).read_text(),Loader=yaml.BaseLoader)
            admission=workflow['jobs']['pr-admission'];steps=admission['steps']
            self.assertEqual(steps[0]['continue-on-error'],'true')
            self.assertEqual(steps[0]['with']['fetch-depth'],'2')
            self.assertIn("github.event.action == 'synchronize'",steps[0]['if'])
            self.assertIn('github.event.pull_request.head.repo.id == github.event.repository.id',steps[0]['if'])
            self.assertEqual(steps[1]['if'],'${{ always() }}')
            self.assertIn('skip-heavy=false',steps[1]['run'])
            self.assertIn('CHECKOUT_OUTCOME',steps[1]['run'])

    def test_full_environment_probe_follows_cache_population(self):
        import yaml
        for name,job,cache_name,build_name in [
                ('lean.yml','lean','Get the existing Mathlib cache','Build the full project'),
                ('variable-envelope.yml','variable-envelope','Fetch only the Mathlib cache needed by the isolated VE modules',
                 'Explicit builds, exact regressions, bundled kernel replays and every-declaration axiom audit')]:
            workflow=yaml.load((ROOT/'.github/workflows'/name).read_text(),Loader=yaml.BaseLoader)
            steps=workflow['jobs'][job]['steps']
            index=lambda title: next(i for i,step in enumerate(steps) if step.get('name')==title)
            setup=index('Guard the pinned toolchain for all source compiler children')
            early=index('Verify guarded runtime hashes and environment')
            cache=index(cache_name)
            probe=index('Verify the effective Lake and Lean child environment')
            build=index(build_name)
            self.assertLess(setup,early);self.assertLess(early,cache)
            self.assertLess(cache,probe);self.assertLess(probe,build)
            self.assertNotIn('--probe',steps[early]['run'])
            self.assertIn('audit --probe',steps[probe]['run'])
            final=next(step for step in steps if step.get('id')=='runtime-audit')
            self.assertEqual(final['if'],'${{ always() }}')
            self.assertIn('audit --probe --require-source',final['run'])
            if name=='lean.yml':
                restore=index('Restore the existing Lake cache')
                self.assertLess(early,restore);self.assertLess(restore,cache)

    def test_original_workflow_gates_and_lock_are_preserved(self):
        # BaseLoader treats GitHub's YAML 1.2 `on` as a string, unlike YAML 1.1.
        import yaml
        read=lambda name: yaml.load((ROOT/'.github/workflows'/name).read_text(),Loader=yaml.BaseLoader)
        core=read('lean.yml');ve=read('variable-envelope.yml');caller=read('p0-root-dispatch.yml')
        self.assertIn('workflow_call',core['on'])
        for workflow,job in [(core,'lean'),(ve,'variable-envelope')]:
            heavy=workflow['jobs'][job]
            self.assertEqual(heavy['needs'],'pr-admission')
            self.assertEqual(heavy['if'],"${{ !cancelled() && (needs.pr-admission.result != 'success' || needs.pr-admission.outputs.skip-heavy != 'true') }}")
            self.assertNotIn('concurrency',workflow)
            self.assertNotIn('concurrency',workflow['jobs']['pr-admission'])
            self.assertIn(workflow['on']['pull_request'], ('', None))
            self.assertIn('pull_request',workflow['on']);self.assertIn('workflow_dispatch',workflow['on'])
            self.assertEqual(workflow['on']['push']['branches-ignore'],['codex/chen-parts-integration'])
            self.assertEqual(workflow['on']['push']['paths-ignore'],['automation/**'])
            self.assertEqual(heavy['concurrency'],{'group':'goldbach-p0-heavy','cancel-in-progress':'false'})
        self.assertEqual(caller['on'],{'push':{'branches':['codex/chen-parts-integration'],
                                             'paths':['automation/root-dispatch.json']}})
        self.assertEqual(caller['permissions'],{'contents':'read'})
        self.assertNotIn('concurrency',caller)
        self.assertEqual(caller['jobs']['full-root'],{'needs':'admission','uses':'./.github/workflows/lean.yml'})
        admission=caller['jobs']['admission']
        self.assertNotIn('concurrency',admission)
        self.assertEqual(admission['steps'][0]['with']['fetch-depth'],'2')
        code=admission['steps'][1]['run']
        self.assertIn("== [head, before]",code)
        self.assertIn("paths == ['automation/root-dispatch.json']",code)
        self.assertIn("'--no-renames'",code)
        steps=core['jobs']['lean']['steps'];by_id={s['id']:s for s in steps if 'id'in s}
        for name in ('build','leanchecker','axiom-audit','round3-types','round4-targets','round4-types','round6-types'):
            self.assertIn(name,by_id)
        outcomes=next(s for s in steps if s.get('name')=='Record required verification outcomes')['run']
        for name in ('BUILD','LEANCHECKER','AXIOM_AUDIT','ROUND3_TYPES','ROUND4_TARGETS','ROUND4_TYPES','ROUND6_TYPES','RUNTIME'):
            self.assertIn('test "$'+name+'_OUTCOME" = success',outcomes)
        self.assertTrue(all('p0-ci-shadow-toolchain' not in str(s.get('with',{}).get('path','')) for s in steps))

if __name__ == '__main__':
    unittest.main(verbosity=2)
