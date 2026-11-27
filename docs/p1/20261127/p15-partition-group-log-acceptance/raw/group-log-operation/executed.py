"""New GroupLog owner, original Variation dependency, immutable receipt replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PACKET = 'docs/p1/20261127/p15-group-log-abel'
TARGET = 'ImbalancedChen.P5OriginalGroupLogAbelVariation'
DEPENDENCY = 'ImbalancedChen.Part3PrimeMellinProfileVariation'
NAME = TARGET.split('.')[-1] + '.lean'
LIVE = 'ImbalancedChen/' + NAME
BASE = 'f7e9219f4860a819758d52752c5a9309dd14a8c7'
ORIGINAL_PATH = 'docs/source-only/20261102-resume-30k/hb_group_sw/' + NAME
ORIGINAL_SHA = '0cd74710f8ec890412e35e28e3985e9eceff6d52157b12a24c0873d9c50fe3d2'
VAR_ADAPTER = 'docs/p1/20261127/p15-mellin-variation/run_variation.py'
VAR_ADAPTER_SHA = '1c132fefea799e8a3a3127defb07785138e3669e1f80beee2f5aa733b1914f50'
VAR_SOURCE_SHA = 'f57c040a86ad3bda56b21e5fe993a98157de89328862fd741523c3b00191263e'
DECLARATIONS = ('reciprocalGroupLog','normalizedProfile','normalizedProfile_eq_div',
    'reciprocalGroupLog_hasDerivAt','reciprocalGroupLog_contDiffAt','coordinate_mem',
    'log_floor_on_interval','reciprocalGroupLog_bounds','normalizedProfile_hasDerivAt',
    'normalizedProfile_contDiffOn','normalizedProfile_variation_le')
INPUTS = {'source_sha256': 'dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73',
 'source_bytes': 10005,
 'probe': {'job_id': 'job_82e632e67a414c9487d3f1512f4c950e',
           'directory': '/workspace/p1-complete-proof/20261127-p15-group-log-abel-probe-v1/dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73/attempt-00000',
           'source_sha256': 'dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73',
           'source_bytes': 10005,
           'result_bytes': 4108,
           'result_sha256': 'e021795904c208a227df7241b2723c253c716a0502558576c20cb1d700b98ecc',
           'driver_sha256': '3e402aedbd4c923499813ac9ec7c5ed7992f996d81d2e431b5726716cc3914a6',
           'log_sha256': '72cb0e44496fcda72b53492e745f580bb7b2ec2a781581b0d75657c36c524a85'},
 'failed_probes': [{'job_id': 'job_82903d7db9f64614b58e4acf8bdcd896',
                    'directory': '/workspace/p1-complete-proof/20261127-p15-group-log-abel-probe-v1/0cd74710f8ec890412e35e28e3985e9eceff6d52157b12a24c0873d9c50fe3d2/attempt-00000',
                    'source_sha256': '0cd74710f8ec890412e35e28e3985e9eceff6d52157b12a24c0873d9c50fe3d2',
                    'source_bytes': 9607,
                    'result_bytes': 3788,
                    'result_sha256': 'ec0eee88a3948c1976d9af65b7710d9739405facb7a4a339563e6b2ceed3f09b',
                    'driver_sha256': '0473334f72f5efae5742325ee6252f641ab265eefe1ca39e6fd198f6710e056e',
                    'log_sha256': '87664b0dac2c1cb82786eb66a2da552c751eca5474e9721964fbde863f3ebea8',
                    'publication': 'failed-v1'},
                   {'job_id': 'job_d542ab673de745d6b66519f818c9bedf',
                    'directory': '/workspace/p1-complete-proof/20261127-p15-group-log-abel-probe-v1/1f2dabefaaae151805ccf4e82b1f0d2695e8ee5d4859675c3e92aef8b1b367c5/attempt-00000',
                    'source_sha256': '1f2dabefaaae151805ccf4e82b1f0d2695e8ee5d4859675c3e92aef8b1b367c5',
                    'source_bytes': 9851,
                    'result_bytes': 4108,
                    'result_sha256': '9a87133185eae38cdeb3ff2b9feb4be4601aa53513620795b478c9791457b146',
                    'driver_sha256': 'a4dc2174be2dbd525737023f5af58a4d950f2f1ce5abccec73784df563bb0ed9',
                    'log_sha256': '2eabdf8647d143b738c7f9b0fd68d7fa69f8c4e4a1ccec1509267a257ccd1c5e',
                    'publication': 'failed-v2'},
                   {'job_id': 'job_f2e9daf032a4475687dc2c62942a2bac',
                    'directory': '/workspace/p1-complete-proof/20261127-p15-group-log-abel-probe-v1/9f7063ffcf590a2a74e2613176489d725add60557a5458242a53f0aa71f631b7/attempt-00000',
                    'source_sha256': '9f7063ffcf590a2a74e2613176489d725add60557a5458242a53f0aa71f631b7',
                    'source_bytes': 9978,
                    'result_bytes': 4107,
                    'result_sha256': '795349e66e2a3634bc954ea8a51009fbaa5e77d72ee344e9a7c73f691a1468a7',
                    'driver_sha256': '8d3f1ff22a16b7dca671c8197e90b3625b3737a0d37671a229efa04cdc31d573',
                    'log_sha256': '5b37dba8d5d877d2703a6ebd7ff3054bc033a58c26020f5b1af17e80d412c95c',
                    'publication': 'failed-v3'},
                   {'job_id': 'job_dbb5fffce613429ab41a8288ff6028ef',
                    'directory': '/workspace/p1-complete-proof/20261127-p15-group-log-abel-probe-v1/af2136380c1ef8010aedf97acf45f64c9a1453f751217dedf7cfe55b89238449/attempt-00000',
                    'source_sha256': 'af2136380c1ef8010aedf97acf45f64c9a1453f751217dedf7cfe55b89238449',
                    'source_bytes': 9964,
                    'result_bytes': 4108,
                    'result_sha256': 'e52e744571f2a82054c2529bd43543fba921b699254245dd0ac6b223590f0281',
                    'driver_sha256': '88972403d561387f1de9aa128d8b69c3d16d543fa5f22c409d208729babfe571',
                    'log_sha256': '50f26aaaef95b7823807e7607eb1beb037ff52a0c6200ba7440760468c38f4bc',
                    'publication': 'failed-v4'}]}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def git(commit,path):
    return subprocess.check_output(['git','show',commit+':'+path],cwd=REPO)

def regular(path):
    need(path.is_file() and not path.is_symlink(),'expected regular file '+str(path))
    return path.read_bytes()

def interfaces(source):
    text=source.decode(); result={}
    for match in re.finditer(r'^(?:private )?(?:def|theorem) (\w+)\b',text,re.MULTILINE):
        name=match.group(1)
        need(name not in result,'duplicate declaration')
        result[name]=text[match.start():text.index(':=',match.end())]
    need(tuple(result)==DECLARATIONS,'declaration name/order/visibility differs')
    return result

def verify_repair(old,new):
    need(len(old)==9607 and digest(old)==ORIGINAL_SHA,'original GroupLog source differs')
    need(len(new)==INPUTS['source_bytes'] and digest(new)==INPUTS['source_sha256'],'selected GroupLog source differs')
    a,b=interfaces(old),interfaces(new)
    name='normalizedProfile_hasDerivAt'
    before='(deriv (reciprocalGroupLog A) y : ℂ)'
    after='((deriv (reciprocalGroupLog A) y : ℝ) : ℂ)'
    need(a[name].count(before)==1,'original derivative annotation differs')
    a[name]=a[name].replace(before,after)
    need(a==b,'declaration interface differs beyond explicit real derivative cast')

def verified_probe(commit,source,s):
    p=INPUTS['probe']; run=Path(p['directory'])
    need(run.resolve()==run,'probe route contains symlink')
    raw=regular(run/'PROBE_RESULT.json')
    need(raw==git(commit,PACKET+'/probe/PROBE_RESULT.json') and len(raw)==p['result_bytes'] and digest(raw)==p['result_sha256'],'actual probe result differs')
    result=json.loads(raw)
    need(result['schema']=='p15_original_group_log_abel_probe_v1' and result['source_base']==BASE and
         result['original_source_path']==ORIGINAL_PATH and result['original_source_sha256']==ORIGINAL_SHA and
         result['source_sha256']==INPUTS['source_sha256'] and result['source_bytes']==len(source) and
         result['exit_code']==0 and result['probe_passed'] is True and
         result['output_object_requested'] is False and result['new_formal_credit']==0 and
         result['whole_P1_5_complete'] is False,'probe identity/status differs')
    need(regular(run/NAME)==source and git(commit,PACKET+'/probe/'+NAME)==source,'probe source differs')
    driver=regular(run/'probe_driver.py')
    need(driver==git(commit,PACKET+'/probe/probe_driver.py') and digest(driver)==p['driver_sha256'],'probe driver differs')
    cmd=result['command']; log=regular(run/'probe.log')
    need(cmd['argv']==s.h.guard(0,['lake','--no-build','env','lean',str(run/NAME)]) and
         cmd['cwd']==str(PROJECT) and cmd['exit_code']==0 and
         cmd['actual_built_modules']==[] and cmd['actual_failed_modules']==[] and
         cmd['log']==str(run/'probe.log') and len(log)==cmd['log_bytes'] and digest(log)==cmd['log_sha256'] and
         log==git(commit,PACKET+'/probe/probe.log'),'probe command/log differs')
    need(s.api.read_json(run/'PRESERVED_BEFORE.json')==s.api.read_json(run/'PRESERVED_AFTER.json') and
         s.api.read_json(run/'GIT_BEFORE.json')==s.api.read_json(run/'GIT_AFTER.json'),'probe preservation differs')
    worker=['python3','-B',str(run/'probe_driver.py'),'--worker']
    expected=s.h.serialize(0,run/'LANE.json',worker)
    outer=s.api.read_json(run/'serialized-probe-command.json')
    outer_log=regular(run/'serialized-probe.log')
    for rel in ('serialized-probe-command.json','serialized-probe.log','LANE.json'):
        need(regular(run/rel)==git(commit,PACKET+'/probe/'+rel),'outer probe evidence differs: '+rel)
    need(outer['argv']==expected and outer['cwd']==str(PROJECT) and outer['exit_code']==0 and
         outer['actual_built_modules']==[] and outer['actual_failed_modules']==[] and
         outer['log']==str(run/'serialized-probe.log') and
         outer['log_bytes']==len(outer_log) and outer['log_sha256']==digest(outer_log),
         'probe serializer did not finish successfully')
    lane=s.api.read_json(run/'LANE.json')
    state=expected[expected.index('--state')+1]
    need(lane['status']=='VALIDATION_LANE_FINISHED' and lane['exit_code']==0 and
         lane['argv']==worker and lane['state']==state and
         lane['state_sha256']==digest(regular(Path(state))) and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True,
         'probe lane is incomplete or incorrectly bound')
    for f in INPUTS['failed_probes']:
        prior=Path(f['directory']); name=f['publication']
        for rel in ('PROBE_RESULT.json','probe.log',NAME,'probe_driver.py'):
            data=regular(prior/rel)
            need(data==git(commit,PACKET+'/'+name+'/'+rel),'original failed evidence differs: '+rel)
        failed=s.api.read_json(prior/'PROBE_RESULT.json')
        need(failed['exit_code']!=0 and failed['probe_passed'] is False and
             failed['source_sha256']==f['source_sha256'] and
             digest(regular(prior/'PROBE_RESULT.json'))==f['result_sha256'],'failed probe identity differs')
        failed_source=regular(prior/NAME); failed_log=regular(prior/'probe.log')
        fc=failed['command']
        need(digest(failed_source)==f['source_sha256'] and len(failed_source)==failed['source_bytes'] and
             fc['log']==str(prior/'probe.log') and fc['log_bytes']==len(failed_log) and
             fc['log_sha256']==digest(failed_log),'failed probe source/log fingerprint differs')
    need(all(not list(run.glob(x)) for x in ('*.olean*','*.ilean*','*.trace','*.c','*.ir','*.o','*.bc')),'no-output probe contains object')
    return {'job_id':p['job_id'],'directory':str(run),'source_sha256':INPUTS['source_sha256'],
            'result_sha256':p['result_sha256'],'driver_sha256':p['driver_sha256'],'log_sha256':digest(log)}

def load(commit):
    need(isinstance(INPUTS,dict),'UNBOUND: real successful exact-source probe is required')
    need(re.fullmatch('[0-9a-f]{40}',commit) and commit!=BASE,'new full source publication required')
    raw=git(BASE,VAR_ADAPTER)
    need(digest(raw)==VAR_ADAPTER_SHA,'original Variation adapter pin differs')
    v=ModuleType('original_variation_reader')
    v.__file__=str(ROOT/BASE/'published-entrypoints/run_variation.py')
    exec(compile(raw,VAR_ADAPTER,'exec'),v.__dict__)
    vc=v.load(BASE); dependency=v.check(vc)
    need(dependency['status']=='REVALIDATED','Variation original acceptance failed')
    g,s=vc.g,vc.s
    runner=git(commit,PACKET+'/run_group_log.py')
    need(runner==regular(Path(__file__)),'executed adapter differs from publication')
    old=git(BASE,ORIGINAL_PATH); new=git(commit,PACKET+'/'+NAME)
    verify_repair(old,new)
    need(git(commit,LIVE)==new and s.h.imports(new)==[DEPENDENCY],'canonical source/import differs')
    spec=SimpleNamespace(graph={DEPENDENCY:[],TARGET:[DEPENDENCY]},
        sources={DEPENDENCY:VAR_SOURCE_SHA,TARGET:INPUTS['source_sha256']},
        manifest={'project_sources':{DEPENDENCY:{'all_imports':['Mathlib']},TARGET:{'all_imports':[DEPENDENCY]}}})
    base=ROOT/commit
    ident={'commit':commit,'module':TARGET,'old_sha256':ORIGINAL_SHA,'new_sha256':INPUTS['source_sha256'],
        'original_dependency_acceptance':dependency,'independent_no_output_probe':verified_probe(commit,new,s),
        'adapter_sha256':digest(runner),'variation_adapter_sha256':VAR_ADAPTER_SHA,
        'publication':PACKET+'/'+NAME,'whole_P1_5_complete':False}
    return SimpleNamespace(v=v,vc=vc,g=g,s=s,spec=spec,old=old,new=new,ident=ident,
        runner=runner,base=base,run=base/'group-log-operation',commit=commit)

def fixed(c):
    result=c.v.fixed(c.vc)
    result['dependency_original_acceptance']=c.v.accepted(c.vc)
    return result

def accepted(c):
    need(owner_roots(c)==[c.base/TARGET],'owner missing or competing owner exists')
    e=c.g.existing_owner(c.s,c.commit,c.spec,TARGET)
    c.g.require_completed_existing_owner(c.s,c.commit,c.spec,TARGET,e)
    folders=list((c.base/TARGET/'audits').iterdir())
    need(len(folders)==1,'expected exactly one immutable full-owned audit')
    v=c.s.api.read_json(folders[0]/'lane-0/VALIDATION_RESULTS.json')
    recs=c.s.api.read_json(folders[0]/'lane-0/OWNED_EXPORTS.json')
    need(v['only_standard_axioms'] is True and v['full_owned_including_private_generated'] is True and
         v['total_owned_exports']==len(recs) and v['total_public_exports']==sum(not x['is_private'] for x in recs),
         'incomplete full-owned/private audit or nonstandard axioms')
    public={x['name'] for x in recs if not x['is_private']}
    ns='ImbalancedChen.P5Z.OriginalGroupLogAbelVariation.'
    need(all(ns+n in public for n in DECLARATIONS if n!='coordinate_mem'),'missing original public declaration')
    return {'owned':v['total_owned_exports'],'public':v['total_public_exports'],
        'axioms':sorted({a for x in recs for a in x['axioms']}),
        'binding':c.g.acceptance_binding(c.s,c.commit,TARGET)}


def owner_roots(c):
    return [p/TARGET for p in ROOT.iterdir() if p.is_dir() and
            re.fullmatch('[0-9a-f]{40}',p.name) and os.path.lexists(p/TARGET)]


def fresh(c):
    need(not owner_roots(c), 'prior owner found; preserve and inspect')
    c.g.require_fresh_owner(TARGET,c.g.module_artifacts(c.s,TARGET))
    path=PROJECT/LIVE
    state=regular(path) if os.path.lexists(path) else None
    need(state in (None,c.old), 'unexpected live source or prior unpublished installation')
    return state


def read_command(c, directory, name, expected, allowed):
    cmd=c.s.api.read_json(directory/(name+'-command.json'))
    log=directory/(name+'.log')
    need(cmd['argv']==expected and cmd['cwd']==str(PROJECT) and cmd['exit_code']==0 and
         not cmd['actual_failed_modules'] and set(cmd['actual_built_modules'])<=allowed and
         cmd['log']==str(log) and not log.is_symlink() and
         c.s.d.fingerprint(log)=={'sha256':cmd['log_sha256'],'bytes':cmd['log_bytes']},
         'command provenance differs: '+name)
    return cmd


def install(c, prior):
    path=PROJECT/LIVE
    c.s.d.write_frozen(c.run/'original-published.lean',c.old)
    if prior is not None:
        c.s.d.write_frozen(c.run/'original-installed.lean',prior)
    with tempfile.NamedTemporaryFile(dir=path.parent,prefix='.group-log-install-',delete=False) as f:
        tmp=Path(f.name)
        try:
            os.fchmod(f.fileno(),0o644 if prior is None else path.stat().st_mode & 0o777)
            f.write(c.new)
            f.flush()
            os.fsync(f.fileno())
            if prior is None:
                os.link(tmp,path)
            else:
                need(regular(path)==prior, 'live original changed before swap')
                os.replace(tmp,path)
        finally:
            tmp.unlink(missing_ok=True)
    need(regular(path)==c.new,'installed source mismatch')
    fd=os.open(path.parent,os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)
    c.s.d.save(c.run/'INSTALL.json',{'identity':c.ident,'original_present':prior is not None})


def worker(c):
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__)==c.run/'executed.py' and c.run.resolve()==c.run,'invalid worker publication or directory')
    need(c.s.api.read_json(c.run/'GIT_BEFORE.json')==c.s.d.original_git_state(REPO),
         'dispatcher baseline or checkout changed before worker')
    c.s.d.runtime_binding(c.s.h)
    before=fixed(c)
    c.s.d.save(c.run/'PRESERVED_BEFORE.json',before)
    try:
        prior=fresh(c)
        direct=c.g.direct_import_readiness(c.s,c.spec,TARGET,c.run)
        need(fixed(c)==before,'protected state changed during direct-import check')
        need(fresh(c)==prior,'owner/source changed during no-build preflight')
        install(c,prior)
        c.g.run_owner(c.s,c.commit,c.base,c.run,TARGET,c.spec.graph,c.spec.sources)
        a=accepted(c)
    finally:
        after=fixed(c)
        c.s.d.save(c.run/'PRESERVED_AFTER.json',after)
        need(before==after,'protected state changed in worker')
    c.s.d.save(c.run/'WORKER_PASS.json',{'identity':c.ident,'owner':a,'native_stock':direct})


def dispatch(c):
    # mkdir is exclusive. A partial or failing run is evidence and must survive.
    fresh(c)
    need(c.run.resolve()==c.run, 'unexpected symlink in operation route')
    c.run.mkdir(parents=True,exist_ok=False)
    c.s.d.write_frozen(c.run/'executed.py',c.runner)
    before=c.s.d.original_git_state(REPO)
    c.s.d.save(c.run/'GIT_BEFORE.json',before)
    try:
        command=c.s.ops.run(c.run,'serialized-group-log',c.s.h.serialize(0,c.run/'LANE.json',
            ['python3','-B',str(c.run/'executed.py'),'--source-commit',c.commit,'--worker']),relay=True)
        need(command['exit_code']==0 and not command['actual_failed_modules'] and
             set(command['actual_built_modules']) <= {TARGET},'serialized owner failed/scope differed')
        w=c.s.api.read_json(c.run/'WORKER_PASS.json')
        need(w['identity']==c.ident and w['owner']==accepted(c),'incomplete worker evidence')
    finally:
        after=c.s.d.original_git_state(REPO)
        c.s.d.save(c.run/'GIT_AFTER.json',after)
        need(before==after,'evidence checkout Git state changed')
    c.s.d.save(c.run/'PASS.json',{'identity':c.ident,'worker':c.s.d.fingerprint(c.run/'WORKER_PASS.json'),
        'command':command,'preserved':c.s.d.fingerprint(c.run/'PRESERVED_BEFORE.json')})


def check(c):
    need(c.run.resolve()==c.run, 'unexpected symlink in operation route')
    if not os.path.lexists(c.run):
        prior=fresh(c)
        return {'status':'FRESH','identity':c.ident,'old_source_present':prior is not None}
    read=c.s.api.read_json
    need((c.run/'PASS.json').is_file(), 'incomplete or failed operation; inspect '+str(c.run))
    p=read(c.run/'PASS.json')
    need(regular(c.run/'executed.py')==c.runner and regular(c.run/'original-published.lean')==c.old and
         p['identity']==c.ident and p['worker']==c.s.d.fingerprint(c.run/'WORKER_PASS.json'),'dispatch provenance differs')
    installed=read(c.run/'INSTALL.json')
    need(installed['identity']==c.ident and isinstance(installed['original_present'],bool),'install receipt differs')
    backup=c.run/'original-installed.lean'
    need(regular(backup)==c.old if installed['original_present'] else not os.path.lexists(backup),'backup differs')
    w=read(c.run/'WORKER_PASS.json')
    need(w['identity']==c.ident and w['owner']==accepted(c),'full-owned replay differs')
    need(read(c.run/'GIT_BEFORE.json')==read(c.run/'GIT_AFTER.json') and
         p['preserved']==c.s.d.fingerprint(c.run/'PRESERVED_BEFORE.json') and
         p['preserved']==c.s.d.fingerprint(c.run/'PRESERVED_AFTER.json'),'operation preservation differs')
    # These native bindings belonged to the accepted import-only graph. Other owners may be
    # legitimately accepted after this operation, so compare their metadata only before/after it.
    current=fixed(c)
    recorded=read(c.run/'PRESERVED_BEFORE.json')
    need(all(recorded[k]==current[k] for k in ('native','environment','dependency_original_acceptance')),'native stock or environment changed')
    expected=c.s.h.serialize(0,c.run/'LANE.json',['python3','-B',str(c.run/'executed.py'),'--source-commit',c.commit,'--worker'])
    cmd=read_command(c,c.run,'serialized-group-log',expected,{TARGET})
    direct=read_command(c,c.run/TARGET,'direct-import-stock-readiness',
        c.s.h.guard(0,['lake','--no-build','build','+'+DEPENDENCY+':olean']),set())
    need(cmd==p['command'] and direct==w['native_stock'],'serialized/native-stock command differs')
    return {'status':'REVALIDATED','identity':c.ident,'owner':{k:v for k,v in w['owner'].items() if k!='binding'}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit',required=True)
    group=parser.add_mutually_exclusive_group(required=True)
    for mode in ('run','check','worker'):
        group.add_argument('--'+mode,action='store_true')
    args=parser.parse_args()
    c=load(args.source_commit)
    if args.worker:
        worker(c)
    else:
        if args.run:
            dispatch(c)
        print(json.dumps(check(c),sort_keys=True),flush=True)

if __name__=='__main__':
    main()
