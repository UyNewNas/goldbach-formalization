"""One new no-output GroupLog probe; reuse the accepted Variation reader."""
from pathlib import Path
from types import ModuleType
import argparse, hashlib, json, os, re, subprocess, sys

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ACCEPTED = 'f7e9219f4860a819758d52752c5a9309dd14a8c7'
VAR_ADAPTER = 'docs/p1/20261127/p15-mellin-variation/run_variation.py'
VAR_ADAPTER_SHA = '1c132fefea799e8a3a3127defb07785138e3669e1f80beee2f5aa733b1914f50'
ORIGINAL_PATH = 'docs/source-only/20261102-resume-30k/hb_group_sw/P5OriginalGroupLogAbelVariation.lean'
ORIGINAL_SHA = '0cd74710f8ec890412e35e28e3985e9eceff6d52157b12a24c0873d9c50fe3d2'
SOURCE_SHA = 'dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73'
SOURCE_BYTES = 10005
TARGET = 'ImbalancedChen.P5OriginalGroupLogAbelVariation'
NAME = 'P5OriginalGroupLogAbelVariation.lean'
ROOT = Path('/workspace/p1-complete-proof/20261127-p15-group-log-abel-probe-v1')
RUN = ROOT / SOURCE_SHA / 'attempt-00000'
INPUT = Path('/workspace/p1-complete-proof/p15-staged-scripts') / ('group_log_' + SOURCE_SHA + '.lean')
PREVIOUS_FAILURE = {'task_id':'job_dbb5fffce613429ab41a8288ff6028ef','source_sha256':'af2136380c1ef8010aedf97acf45f64c9a1453f751217dedf7cfe55b89238449','result_sha256':'e52e744571f2a82054c2529bd43543fba921b699254245dd0ac6b223590f0281','log_sha256':'50f26aaaef95b7823807e7607eb1beb037ff52a0c6200ba7440760468c38f4bc'}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def regular(p):
    need(p.is_file() and not p.is_symlink(), 'expected regular file: '+str(p))
    return p.read_bytes()

def load():
    raw=subprocess.check_output(['git','show',ACCEPTED+':'+VAR_ADAPTER],cwd=REPO)
    need(sha(raw)==VAR_ADAPTER_SHA,'original Variation adapter pin differs')
    v=ModuleType('accepted_variation_reader')
    v.__file__=str(Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')/ACCEPTED/'published-entrypoints/run_variation.py')
    exec(compile(raw,VAR_ADAPTER,'exec'),v.__dict__)
    c=v.load(ACCEPTED)
    accepted=v.check(c)
    need(accepted['status']=='REVALIDATED','original Variation is not accepted')
    original=v.git(ACCEPTED,ORIGINAL_PATH)
    need(sha(original)==ORIGINAL_SHA and len(original)==9607,'original source pin differs')
    source=regular(INPUT)
    need(sha(source)==SOURCE_SHA and len(source)==SOURCE_BYTES,'selected source pin differs')
    need(c.s.h.imports(source)==['ImbalancedChen.Part3PrimeMellinProfileVariation'],'unexpected imports')
    return v,c,source,accepted

def fresh(v,c):
    roots=[p/TARGET for p in v.ROOT.iterdir() if p.is_dir() and re.fullmatch('[0-9a-f]{40}',p.name) and os.path.lexists(p/TARGET)]
    need(not roots,'existing owner requires reuse inspection')
    c.g.require_fresh_owner(TARGET,c.g.module_artifacts(c.s,TARGET))
    need(not os.path.lexists(PROJECT/'ImbalancedChen'/NAME),'unexpected installed target source')

def fixed(v,c):
    return {'existing':v.fixed(c),'accepted_variation':v.accepted(c)}

def worker(v,c,source,accepted):
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__)==RUN/'probe_driver.py' and RUN.resolve()==RUN,'unexpected worker path')
    need(c.s.api.read_json(RUN/'GIT_BEFORE.json')==c.s.d.original_git_state(REPO),'checkout changed before worker')
    need(regular(RUN/NAME)==source,'probe source differs')
    fresh(v,c)
    before=fixed(v,c)
    c.s.d.save(RUN/'PRESERVED_BEFORE.json',before)
    cmd=None
    try:
        cmd=c.s.ops.run(RUN,'probe',c.s.h.guard(0,['lake','--no-build','env','lean',str(RUN/NAME)]),cwd=PROJECT,relay=True)
        need(not cmd['actual_built_modules'] and not cmd['actual_failed_modules'],'probe attempted a dependency build')
    finally:
        after=fixed(v,c)
        c.s.d.save(RUN/'PRESERVED_AFTER.json',after)
        need(before==after,'protected acceptance/source/artifacts changed')
        fresh(v,c)
    result={'schema':'p15_original_group_log_abel_probe_v1','source_base':ACCEPTED,
        'original_source_path':ORIGINAL_PATH,'original_source_sha256':ORIGINAL_SHA,
        'source_sha256':SOURCE_SHA,'source_bytes':SOURCE_BYTES,'previous_failure':PREVIOUS_FAILURE,
        'dependency_original_acceptance':accepted,'command':cmd,
        'exit_code':cmd['exit_code'],'probe_passed':cmd['exit_code']==0,
        'output_object_requested':False,'new_formal_credit':0,'whole_P1_5_complete':False}
    c.s.d.save(RUN/'PROBE_RESULT.json',result)
    print(json.dumps(result,sort_keys=True),flush=True)
    return cmd['exit_code']

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--worker',action='store_true');args=p.parse_args()
    v,c,source,accepted=load()
    if args.worker:
        return worker(v,c,source,accepted)
    fresh(v,c)
    need(RUN.resolve()==RUN,'symlink in probe root')
    RUN.mkdir(parents=True,exist_ok=False)
    c.s.d.write_frozen(RUN/'probe_driver.py',regular(Path(__file__)))
    c.s.d.write_frozen(RUN/NAME,source)
    before=c.s.d.original_git_state(REPO)
    c.s.d.save(RUN/'GIT_BEFORE.json',before)
    try:
        cmd=c.s.ops.run(RUN,'serialized-probe',c.s.h.serialize(0,RUN/'LANE.json',['python3','-B',str(RUN/'probe_driver.py'),'--worker']),cwd=PROJECT,relay=True)
    finally:
        after=c.s.d.original_git_state(REPO)
        c.s.d.save(RUN/'GIT_AFTER.json',after)
        need(before==after,'original checkout Git state changed')
    result=c.s.api.read_json(RUN/'PROBE_RESULT.json')
    need(result['exit_code']==cmd['exit_code'],'probe terminal exit differs')
    print(json.dumps({'status':'PASSED' if cmd['exit_code']==0 else 'FAILED','run':str(RUN),'result_sha256':sha(regular(RUN/'PROBE_RESULT.json')),'source_sha256':SOURCE_SHA,'exit_code':cmd['exit_code'],'new_formal_credit':0},sort_keys=True),flush=True)
    print('ORIGINAL_LOG_TAIL_BEGIN probe.log',flush=True)
    print(regular(RUN/'probe.log').decode('utf-8',errors='replace')[-24000:],flush=True)
    print('ORIGINAL_LOG_TAIL_END probe.log',flush=True)
    return cmd['exit_code']

if __name__=='__main__':
    raise SystemExit(main())
