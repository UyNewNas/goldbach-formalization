#!/usr/bin/env python3
from pathlib import Path
import os, subprocess, json, hashlib, sys, shutil, datetime
commit=sys.argv[1] if len(sys.argv)==2 else ''
require_commit_chars='0123456789abcdef'
if len(commit)!=40 or any(c not in require_commit_chars for c in commit):
    raise SystemExit('Expected one full pinned commit SHA')
base='8657cfffef159185f73c6a04ae4d31c846c0d0a9'
repo=Path('/workspace/goldbach-p3')
root=Path('/workspace/p25-q96-20261125')
baseline=Path('/workspace/p25-q96-baseline-8657')
mathlib=Path('/mathlib')
alias=Path('/workspace/compile-deps/mathlib')
lean=Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
checker=lean.with_name('leanchecker')
def output(args,cwd=None):
    return subprocess.check_output(args,cwd=cwd,text=True).strip()
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def saved(path,value):
    tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
    tmp.replace(path)
require(output(['git','rev-parse','HEAD'],mathlib)=='e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','Mathlib pin differs')
require(lean.is_file() and checker.is_file(),'Missing pinned compiler/checker')
version=output([str(lean),'--version'])
require('4.33.0-rc1' in version and '62eed1db4d67327ec8120be05f1a1b0847d74561' in version,'Lean version differs')
if os.path.lexists(alias):
    require(alias.resolve()==mathlib.resolve(),'Existing Mathlib alias selects another directory')
else:
    alias.parent.mkdir(parents=True,exist_ok=True)
    alias.symlink_to(mathlib,target_is_directory=True)
# The pinned bootstrap normally fetched this exact object already.
if subprocess.run(['git','cat-file','-e',commit+'^{commit}'],cwd=repo,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0:
    subprocess.check_call(['git','fetch','--negotiation-tip=ed5bd7df3d031a1326f3c1d3b783c186df39425e','origin',commit],cwd=repo)
def worktree(path,head):
    if path.exists():
        require((path/'.git').exists(),'Existing directory is not the expected worktree')
        require(output(['git','rev-parse','HEAD'],path)==head,'Existing worktree has another HEAD')
    else:
        subprocess.check_call(['git','worktree','add','--detach',str(path),head],cwd=repo)
    require(not output(['git','status','--porcelain','--untracked-files=no'],path),'Dirty tracked worktree')
    require(not output(['git','rev-parse','--show-superproject-working-tree'],path),'Unexpected submodule')
worktree(baseline,base)
# Continue only this task's prior clean worktree; preserve all objects and receipts.
if root.exists():
    require(output(['git','rev-parse','HEAD'],root)=='ed5bd7df3d031a1326f3c1d3b783c186df39425e','Unexpected previous finite worktree HEAD')
    require(not output(['git','status','--porcelain','--untracked-files=no'],root),'Dirty tracked finite worktree')
    subprocess.check_call(['git','merge-base','--is-ancestor','ed5bd7df3d031a1326f3c1d3b783c186df39425e',commit],cwd=repo)
    subprocess.check_call(['git','checkout','--detach',commit],cwd=root)
worktree(root,commit)
os.chdir(root)
out=root/'.lake/p25-finite-archive/attempt-003'
require(not out.exists(),'This continuation attempt already exists; inspect its receipts before any retry')
out.mkdir(parents=True,exist_ok=True)
receipt=out/'INPUT_BOUND_ACCEPTANCE.json'
modules=['ImbalancedChen.P2OriginalSaving16Q96FloorCore','ImbalancedChen.P2OriginalSaving19SourceJson','ImbalancedChen.P2OriginalSaving16FiniteArchive']
paths=['/mathlib/.lake/build/lib/lean']+[f'/mathlib/.lake/packages/{p}/.lake/build/lib/lean' for p in ['plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries']]
# Physical inventory task 303440db6f764a54b5c1a1369a42edb7 found Cli unbuilt.
# Its nonexistent directory is omitted; any actual missing import still fails in Lean.
require(all(Path(p).is_dir() for p in paths),'Missing approved Mathlib package path: '+str([p for p in paths if not Path(p).is_dir()]))
env=dict(os.environ);env['LEAN_PATH']=':'.join(paths)
source_map=json.loads(Path('docs/source-only/20261125-p2-5-finite-archive/FINITE_SOURCE_CLOSURE.json').read_text())
source_before={}
for row in source_map['project_modules']:
    actual=sha(row['production_path']);require(actual==row['sha256'],'Finite source map mismatch')
    source_before[row['module']]=actual
require(set(source_before)==set(modules),'Unexpected finite project closure')
prior_records=json.loads(Path('.lake/p2-private/records.json').read_text())
finite_module=modules[-1]
prior_finite=prior_records.get(finite_module,{})
require(prior_finite.get('exit_code')!=0 or prior_finite.get('source_sha256')!=source_before[finite_module],
        'Finite root has a successful current-source record; inspect original input binding before deciding reuse')
require(not (baseline/'.lake/build/lib/lean').exists(),'Unexpected baseline objects in the isolated empty baseline')
manifest=Path('docs/verification/20261125-p2-5-saving16/Q96_EXISTING_INPUTS_AND_SOURCES.json')
manifest_sha='79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0'
require(sha(manifest)==manifest_sha,'Original input manifest differs')
rows=json.loads(manifest.read_text())['saving16_inputs']
data_dir=(root/'../goldbach-research').resolve()
def input_snapshot():
    require(not (root/'../goldbach-research').is_symlink(),'Input directory is a symlink')
    ds=data_dir.stat()
    result={'cwd':str(root),'directory':str(data_dir),'directory_realpath':str(data_dir.resolve()),'directory_identity':{'device':ds.st_dev,'inode':ds.st_ino,'mtime_ns':ds.st_mtime_ns,'ctime_ns':ds.st_ctime_ns},'files':[]}
    for row in rows:
        p=root/row['install_path'];require(not p.is_symlink(),'Input file is a symlink')
        st=p.stat();actual=sha(p)
        require(st.st_size==row['bytes'] and actual==row['sha256'],'Original input changed: '+str(p))
        result['files'].append({'install_path':row['install_path'],'realpath':str(p.resolve()),'bytes':st.st_size,'sha256':actual,'device':st.st_dev,'inode':st.st_ino,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns})
    require(len(result['files'])==14,'Expected fourteen original inputs')
    return result
state={'schema':'p25-original-finite-input-bound-acceptance-v1','accepted':False,'status':'PREPARING_ORIGINAL_INPUTS','source_commit':commit,'source_tree':output(['git','rev-parse','HEAD^{tree}'],root),'baseline_commit':base,'source_sha256':source_before,'manifest_sha256':manifest_sha,'lean_version':version,'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),'mathlib_pin':output(['git','rev-parse','HEAD'],mathlib),'mathlib_realpath':str(alias.resolve()),'approved_LEAN_PATH':env['LEAN_PATH'],'source_map_sha256':sha('docs/source-only/20261125-p2-5-finite-archive/FINITE_SOURCE_CLOSURE.json'),'fresh_finite_compile_required':True,'prior_compilation_records':prior_records,'reuse_boundary':'The unchanged accepted floor core and source/dependency-bound helper records may be reused; the failed or source-changed finite root must compile under this new original-input snapshot.','read_window_condition':'This task is the service single active job. After original-byte preparation, no task subprocess writes the input directory or files. The compiler source reader only reads them. Acceptance assumes no out-of-band host writes; physical identities and content hashes are checked before/after.','replay_boundary':'Kernel replay checks embedded literals and proof objects, and inherits the original fresh data-to-object binding; it does not reread the source JSON.','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
saved(receipt,state)
prepare=[sys.executable,'docs/verification/20261125-p2-5-saving16/prepare-q96-original-inputs.py']
with (out/'INPUT_PREPARATION.log').open('w') as f:
    prep_rc=subprocess.call(prepare,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
print('P25_ORIGINAL_INPUT_PREPARATION_EXIT',prep_rc,flush=True)
print((out/'INPUT_PREPARATION.log').read_text(),flush=True)
state['input_preparation_exit']=prep_rc
state['input_preparation_log_sha256']=sha(out/'INPUT_PREPARATION.log')
saved(receipt,state)
require(prep_rc==0,'Original input preparation failed')
before=input_snapshot();state['input_snapshot_before']=before
state['input_content_binding_sha256']=hashlib.sha256(json.dumps([{'path':r['install_path'],'bytes':r['bytes'],'sha256':r['sha256']} for r in rows],sort_keys=True,separators=(',',':')).encode()).hexdigest()
# The previous SourceJson object failed its full-owned gate on generated partial helpers.
# Verify the changed parser first, before launching the large original finite guards.
state['status']='PARSER_PREREQUISITE_STRICT_COMPILE_RUNNING';saved(receipt,state)
parser_compile=[sys.executable,'verification/part2/run_winner9_private_checks.py',modules[1],
    '--baseline-root',str(baseline),'--workers','1','--threads','1','--memory-mb','11264','--time-budget-seconds','200']
state['parser_compile_command']=parser_compile
state['parser_compile_exit']=subprocess.call(parser_compile,cwd=root,env=env)
saved(receipt,state)
require(state['parser_compile_exit']==0,'Parser prerequisite compile failed; finite guards not started')
parser_audit=[sys.executable,'verification/part2/run_winner9_private_audit.py',modules[1],
    '--summary-name','p25-original-parser-prerequisite-audit.json','--memory-mb','11264']
state['parser_audit_command']=parser_audit
state['status']='PARSER_PREREQUISITE_INDEPENDENT_REPLAY_AND_OWNED_AUDIT_RUNNING';saved(receipt,state)
state['parser_audit_exit']=subprocess.call(parser_audit,cwd=root,env=env)
parser_summary=Path('.lake/p2-private/audit/p25-original-parser-prerequisite-audit.json')
state['parser_audit_summary']=json.loads(parser_summary.read_text()) if parser_summary.exists() else None
saved(receipt,state)
if state['parser_audit_exit']!=0:
    q=Path('.lake/p2-private/audit')/modules[1]/'latest.json'
    if q.exists():
        details=json.loads(q.read_text()); log=details.get('audit',{}).get('log')
        if log and Path(log).is_file():print('P25_PARSER_AUDIT_DIAGNOSTICS '+Path(log).read_text()[-24000:],flush=True)
require(state['parser_audit_exit']==0 and state['parser_audit_summary'] and
        state['parser_audit_summary'].get('all_accepted'),'Parser prerequisite audit failed; finite guards not started')
state['status']='FRESH_FINITE_STRICT_COMPILE_RUNNING';saved(receipt,state)
compile_cmd=[sys.executable,'verification/part2/run_winner9_private_checks.py','ImbalancedChen.P2OriginalSaving16FiniteArchive','--baseline-root',str(baseline),'--workers','1','--threads','1','--memory-mb','11264','--time-budget-seconds','1000']
state['compile_command']=compile_cmd;saved(receipt,state)
# new_strict_compile is a historical record flag, so also require this
# invocation's actual START line; probe/cache adoption does not emit it.
finite_started=False
compile_log=out/'FINITE_STRICT_COMPILE.log'
with compile_log.open('w') as log:
    proc=subprocess.Popen(compile_cmd,cwd=root,env=env,stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,text=True)
    require(proc.stdout is not None,'Missing finite compilation output stream')
    for line in proc.stdout:
        log.write(line);log.flush()
        print(line,end='',flush=True)
        if line.rstrip('\r\n')=='START '+finite_module:
            finite_started=True
    compile_rc=proc.wait()
state['finite_compile_started_this_attempt']=finite_started
state['finite_compile_log_sha256']=sha(compile_log)
after=input_snapshot()
state.update(compile_exit=compile_rc,input_snapshot_after_compile=after,inputs_unchanged_through_compile=(after==before))
records_path=Path('.lake/p2-private/records.json')
records=json.loads(records_path.read_text()) if records_path.exists() else {}
state['compile_records']={m:records.get(m) for m in modules}
state['compiled_objects']={}
for m in modules:
    p=Path('.lake/p2-private/lib')/(m.replace('.','/')+'.olean')
    if p.is_file():state['compiled_objects'][m]={'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
state['fresh_data_to_object_bound']=bool(compile_rc==0 and finite_started and after==before and
    all(records.get(m,{}).get('exit_code')==0 for m in modules) and
    records[finite_module].get('new_strict_compile') is True and
    records[finite_module].get('source_sha256')==source_before[finite_module] and
    finite_module in state['compiled_objects'])
state['status']='COMPILE_FINISHED_AUDIT_PENDING';saved(receipt,state)
require(after==before,'Inputs changed during compilation; outer acceptance is false')
audit_cmd=[sys.executable,'verification/part2/run_winner9_private_audit.py',*modules,'--summary-name','p25-original-finite-owned-audit.json','--memory-mb','11264']
state['audit_command']=audit_cmd;state['status']='INDEPENDENT_REPLAY_AND_OWNED_AUDIT_RUNNING';saved(receipt,state)
audit_rc=subprocess.call(audit_cmd,cwd=root,env=env)
audit_summary=Path('.lake/p2-private/audit/p25-original-finite-owned-audit.json')
state['audit_exit']=audit_rc
if audit_rc!=0:
    for m in modules:
        q=Path('.lake/p2-private/audit')/m/'latest.json'
        if q.exists():
            details=json.loads(q.read_text());log=details.get('audit',{}).get('log')
            if not details.get('accepted') and log and Path(log).is_file():
                print('P25_FAILED_AUDIT_DIAGNOSTICS '+m+' '+Path(log).read_text()[-24000:],flush=True)
state['audit_summary']=json.loads(audit_summary.read_text()) if audit_summary.exists() else None
state['owned_receipts']={}
for m in modules:
    p=Path('.lake/p2-private/audit')/m/'latest.json'
    if p.is_file():state['owned_receipts'][m]={'path':str(p),'sha256':sha(p),'receipt':json.loads(p.read_text())}
final=input_snapshot();state['input_snapshot_after_audit']=final
source_after={m:sha(m.replace('.','/')+'.lean') for m in modules}
state.update(source_sha256_after=source_after,inputs_unchanged_through_audit=(final==before),ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),disk_free_end=shutil.disk_usage(root).free)
state['accepted']=bool(state['fresh_data_to_object_bound'] and audit_rc==0 and final==before and source_after==source_before and state['audit_summary'] and state['audit_summary'].get('all_accepted'))
state['status']='FINITE_INPUT_BOUND_COMPILE_REPLAY_AND_OWNED_AUDIT_ACCEPTED' if state['accepted'] else 'FINITE_CHECK_INCOMPLETE_OR_FAILED'
saved(receipt,state)
print('P25_FINITE_RESULT '+json.dumps({k:state[k] for k in ['status','accepted','source_commit','compile_exit','audit_exit','fresh_data_to_object_bound','inputs_unchanged_through_audit']}),flush=True)
print('P25_FINITE_RECEIPT '+str(receipt)+' '+sha(receipt),flush=True)
sys.exit(0 if state['accepted'] else 1)
