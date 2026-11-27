"""Single-owner source installation, guarded build/kernel audit and readonly replay."""
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
PACKET = 'docs/p1/20261127/p15-mellin-variation'
TARGET = 'ImbalancedChen.Part3PrimeMellinProfileVariation'
NAME = TARGET.split('.')[-1] + '.lean'
LIVE = 'ImbalancedChen/' + NAME
BASE = '040d46058821746c69c5183b3f6c22792287c4ba'
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
DRIVER_SHA = '0440906dfc3caa894ff7226e53ad42be54adda1d5879bd1a72cad578a3b3612d'
OLD_SHA = '2146552e2b0e5fcbe8a3ef40626e3dc957ce4721b02e026ba699470550276d75'
FAILED_V1_SHA = 'fd9ae7288986c4f7545869cbc62a3415f53eff76b95f533342f1331299cb03dd'
FAILED_V1_LOG = 'ff2eea22116aafda693f97cdde1d1952c9a3ff66288f10fbe92ba310c7d77eed'
FAILED_V2_SHA = 'd677b08c1207d10454dc775882f47be82ed8c6cb41a5c6e3ff13b47f9e27474d'
FAILED_V2_LOG = '13da2449ee5e8326249b3079c14f5b657ca014aa790202dc4b1231a1ed3cb0be'
NEW_SHA = 'f57c040a86ad3bda56b21e5fe993a98157de89328862fd741523c3b00191263e'
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-mellin-variation-mathlib-probe-v3')
# Exact original no-output receipt bytes exported from the successful private task.
PROBE_RESULT_SHA = 'c516fde8c95f1dddd233b6dc67eb8469ced1bfffd1d715d63f56381a9d2299b0'
PROBE_RESULT_BYTES = 2280
PROBE_DRIVER_SHA = '4b04a9558df77b6b94b928864f088ce3cddf44626d3c773e34b4844b8cb8a27e'
PROBE_DRIVER_PATH = Path('/workspace/p1-complete-proof/p15-staged-scripts/probe_mathlib_variation_f57c040a.py')
PROBE_JOB_ID = 'job_2ee744896a4f4858b50bd089af2f2a91'
DECLARATIONS = ('phase', 'profile', 'physicalProfile', 'phase_norm', 'phase_hasDerivAt',
                'profile_hasDerivAt', 'profile_contDiffOn', 'profile_deriv_norm_le',
                'normalized_mem', 'physicalProfile_contDiffOn', 'physicalProfile_hasDerivAt',
                'physicalProfile_variation_le')
EXTRA = ('ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry',
         'ImbalancedChen.P1OriginalHistoricalCoefficientDictionary')


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(b):
    return hashlib.sha256(b).hexdigest()


def git(commit, path):
    return subprocess.check_output(['git','show',commit + ':' + path], cwd=REPO)


def regular(p):
    need(p.is_file() and not p.is_symlink(), 'expected regular file ' + str(p))
    return p.read_bytes()


def interfaces(source):
    # All twelve pinned declarations have an explicit ':=' before their bodies.
    text = source.decode()
    headers = {}
    for match in re.finditer(r'^(?:private )?(?:def|theorem) (\w+)\b', text, re.MULTILINE):
        name = match.group(1)
        need(name not in headers, 'duplicate declaration: ' + name)
        headers[name] = text[match.start():text.index(':=', match.end())]
    need(tuple(headers) == DECLARATIONS, 'declaration order, spelling or census differs')
    return headers


def verify_repair(old, failed, failure_log, failed_v2, v2_log, new):
    need(digest(old) == OLD_SHA and len(old) == 6893, 'original source differs')
    need(digest(failed) == FAILED_V1_SHA and len(failed) == 6717 and
         failed == b'import Mathlib\n\n' + old.split(b'\n\n', 1)[1], 'failed v1 preimage differs')
    need(digest(failure_log) == FAILED_V1_LOG and len(failure_log) == 3190, 'original v1 failure log differs')
    need(digest(failed_v2) == FAILED_V2_SHA and len(failed_v2) == 6863 and
         digest(v2_log) == FAILED_V2_LOG and len(v2_log) == 839, 'original v2 source or failure log differs')
    need(digest(new) == NEW_SHA and len(new) == 6869, 'selected repair source differs')
    prior = interfaces(old)
    revised = interfaces(new)
    name = 'profile_hasDerivAt'
    annotation = '(deriv Phi x : ℂ)'
    need(prior[name].count(annotation) == 1, 'original derivative annotation differs')
    prior[name] = prior[name].replace(annotation, '((deriv Phi x : ℝ) : ℂ)')
    need(prior == revised, 'original declaration interface differs beyond the reviewed real cast')


def verified_probe(commit, source, helpers):
    need(PROBE_RESULT_BYTES and PROBE_RESULT_SHA and PROBE_DRIVER_SHA and PROBE_JOB_ID,
         'UNPROBED: a real successful probe for the exact selected source is required')
    run = PROBE_ROOT / NEW_SHA / 'runs' / 'attempt-00000'
    need(run.resolve() == run, 'probe root contains a symlink')
    published = git(commit, PACKET + '/probe/PROBE_RESULT.json')
    result_bytes = regular(run / 'PROBE_RESULT.json')
    need(result_bytes == published and len(result_bytes) == PROBE_RESULT_BYTES and
         digest(result_bytes) == PROBE_RESULT_SHA, 'actual probe result pin differs')
    driver = git(commit, PACKET + '/probe/probe_driver.py')
    need(digest(driver) == PROBE_DRIVER_SHA and regular(PROBE_DRIVER_PATH) == driver,
         'published or staged original probe driver differs')
    result = json.loads(result_bytes)
    lane = run / 'PROBE_LANE.json'
    original_source = run / NAME
    guard = helpers.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(original_source)])
    expected_argv = helpers.h.serialize(0, lane, guard)
    need(result['schema'] == 'p15_mellin_variation_mathlib_only_probe_v3' and
         result['previous_failed_task'] == 'job_a24eb1c578aa420083048ec97e864642' and
         result['previous_failed_source_sha256'] == FAILED_V2_SHA and
         result['proof_body_unchanged'] is False and result['final_conclusion_unchanged'] is True and
         regular(original_source) == source and result['argv'] == expected_argv and
         result['cwd'] == str(PROJECT) and result['source_commit_base'] == BASE and
         result['source_sha256'] == NEW_SHA and result['source_bytes'] == len(source) and
         result['original_source_sha256'] == OLD_SHA and result['imports'] == ['Mathlib'] and
         result['project_dependencies'] == [] and result['exit_code'] == 0 and result['probe_passed'] is True and
         result['output_object_requested'] is False and result['new_owner_accepted'] is False and
         result['whole_P1_5_complete'] is False, 'probe command, source or status differs')
    log = regular(run / 'probe.log')
    need(result['log_path'] == str(run / 'probe.log') and len(log) == result['log_bytes'] and
         digest(log) == result['log_sha256'] and git(commit, PACKET + '/probe/probe.log') == log,
         'original compiler log differs')
    need(all(not list(run.glob(pattern)) for pattern in ('*.olean*','*.ilean*','*.c','*.bc','*.o','*.ir','*.trace')),
         'no-output probe directory contains an object')
    return {'job_id':PROBE_JOB_ID, 'directory':str(run), 'source_sha256':NEW_SHA,
            'result_sha256':PROBE_RESULT_SHA, 'driver_sha256':PROBE_DRIVER_SHA,
            'log_sha256':digest(log), 'output_object_requested':False, 'formal_owner_accepted':False}


def load(commit):
    need(re.fullmatch('[0-9a-f]{40}',commit), 'require full source publication commit')
    raw = git(AG,DRIVER)
    need(digest(raw)==DRIVER_SHA, 'AG driver pin')
    g = ModuleType('frozen_variation_driver')
    g.__file__ = DRIVER
    exec(compile(raw,DRIVER,'exec'),g.__dict__)
    need((g.REPO,g.PROJECT,g.ROOT)==(REPO,PROJECT,ROOT), 'unexpected environment')
    s = g.helpers()
    runner = git(commit,PACKET+'/run_variation.py')
    need(runner==regular(Path(__file__)), 'executed adapter differs from exact publication')
    old = git(BASE,LIVE)
    new = git(commit,PACKET+'/'+NAME)
    verify_repair(old,git(commit,PACKET+'/failed-v1/'+NAME),
                  git(commit,PACKET+'/failed-v1/probe-v1.log'),git(commit,PACKET+'/failed-v2/'+NAME),
                  git(commit,PACKET+'/failed-v2/probe-v2.log'),new)
    need(git(commit,LIVE)==new, 'published canonical Variation differs from selected candidate')
    consumer='ImbalancedChen/Part3MellinPrimeIntervalSW.lean'
    companion=git(commit,consumer)
    prior_consumer=git(BASE,consumer)
    need(digest(prior_consumer)=='77765a39e751cae993f21ec970f7bb075c01922ca0e25e0f5ab4ed241727f0d0' and
         digest(companion)=='20bd87a034f26d0d655507d2b24bf43a50076de19317c1fa0b618b6377ac4016' and
         prior_consumer.split(b'\n\n',1)[1]==companion.split(b'\n\n',1)[1],
         'published consumer import-only compatibility source differs')
    need(s.h.imports(new)==['Mathlib'], 'native-only leaf import differs')
    spec = SimpleNamespace(graph={TARGET:[]},sources={TARGET:NEW_SHA},
                manifest={'project_sources':{TARGET:{'all_imports':['Mathlib']}}})
    base = ROOT/commit
    ident = {'commit':commit,'module':TARGET,'old_sha256':OLD_SHA,'new_sha256':NEW_SHA,
             'failed_v1_source_sha256':FAILED_V1_SHA,'failed_v1_log_sha256':FAILED_V1_LOG,
             'failed_v2_source_sha256':FAILED_V2_SHA,'failed_v2_log_sha256':FAILED_V2_LOG,
             'independent_no_output_probe':verified_probe(commit,new,s),
             'consumer_source_only_sha256':digest(companion),'consumer_compiled':False,
             'publication':PACKET+'/'+NAME,'driver_sha256':DRIVER_SHA,'adapter_sha256':digest(runner)}
    review=json.loads(g.pinned(AG,g.REVIEW,g.REVIEW_SHA))
    return SimpleNamespace(g=g,s=s,spec=spec,review=review,old=old,new=new,ident=ident,runner=runner,
                           base=base,run=base/'variation-operation',commit=commit)


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


def fixed(c):
    # Direct native stock input plus unchanged protected source/artifact metadata.
    native=PROJECT/'.lake/packages/mathlib/.lake/build/lib/lean'
    data={str(native/n):c.s.d.fingerprint(native/n) for n in ('Mathlib.olean','Mathlib.trace')}
    protected={}
    for m in (*c.g.TARGETS,*EXTRA):
        for rel in [c.s.h.module_path(m),*c.g.artifact_paths(m)]:
            path=PROJECT/rel
            st=path.lstat() if os.path.lexists(path) else None
            protected[str(rel)]=[st.st_dev,st.st_ino,st.st_mode,st.st_size,st.st_mtime_ns,st.st_ctime_ns] if st else None
    return {'native':data,'environment':c.g.environment(c.s,c.review),'protected_metadata':protected}


def install(c, prior):
    path=PROJECT/LIVE
    c.s.d.write_frozen(c.run/'original-published.lean',c.old)
    if prior is not None:
        c.s.d.write_frozen(c.run/'original-installed.lean',prior)
    with tempfile.NamedTemporaryFile(dir=path.parent,prefix='.mellin-install-',delete=False) as f:
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


def accepted(c):
    need(owner_roots(c)==[c.base/TARGET], 'owner missing or competing prior owner exists')
    e=c.g.existing_owner(c.s,c.commit,c.spec,TARGET)
    c.g.require_completed_existing_owner(c.s,c.commit,c.spec,TARGET,e)
    folders=list((c.base/TARGET/'audits').iterdir())
    need(len(folders)==1,'expected one immutable all-owned audit')
    v=c.s.api.read_json(folders[0]/'lane-0/VALIDATION_RESULTS.json')
    recs=c.s.api.read_json(folders[0]/'lane-0/OWNED_EXPORTS.json')
    need(v['only_standard_axioms'] is True and v['full_owned_including_private_generated'] is True and
         v['total_owned_exports']==len(recs) and v['total_public_exports']==sum(not x['is_private'] for x in recs),
         'incomplete owned/private/kernel or nonstandard axiom receipt')
    public={x['name'] for x in recs if not x['is_private']}
    ns='ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b.'
    required=('phase','profile','physicalProfile','phase_norm','phase_hasDerivAt','profile_hasDerivAt',
              'profile_contDiffOn','profile_deriv_norm_le','physicalProfile_contDiffOn',
              'physicalProfile_hasDerivAt','physicalProfile_variation_le')
    need(all(ns+n in public for n in required), 'missing declared public interface')
    return {'owned':v['total_owned_exports'],'public':v['total_public_exports'],
            'axioms':sorted({a for x in recs for a in x['axioms']}),
            'binding':c.g.acceptance_binding(c.s,c.commit,TARGET)}


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
        command=c.s.ops.run(c.run,'serialized-variation',c.s.h.serialize(0,c.run/'LANE.json',
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
    need(all(recorded[k]==current[k] for k in ('native','environment')),'native stock or environment changed')
    expected=c.s.h.serialize(0,c.run/'LANE.json',['python3','-B',str(c.run/'executed.py'),'--source-commit',c.commit,'--worker'])
    cmd=read_command(c,c.run,'serialized-variation',expected,{TARGET})
    direct=read_command(c,c.run/TARGET,'direct-import-stock-readiness',
        c.s.h.guard(0,['lake','--no-build','build','+Mathlib:olean']),set())
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
