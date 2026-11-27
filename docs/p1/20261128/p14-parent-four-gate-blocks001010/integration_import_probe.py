from pathlib import Path
import os,json,hashlib,subprocess,time
r=Path(__file__).resolve().parent
f=r/'probe.lean';f.write_text('import ImbalancedChen.P5OriginalParentFourGateBlock000\nimport ImbalancedChen.P5OriginalParentFourGateBlocks001010\n#check ImbalancedChen.P5OriginalParentFourGateBlock000.block000_all_child_source_facts\n#check ImbalancedChen.P5OriginalParentFourGateBlocks001010.block001_all_child_source_facts\n#check ImbalancedChen.P5OriginalParentFourGateBlocks001010.block010_all_child_source_facts\n')
source=Path('/workspace/p1-complete-proof/20261128-p14-parent-four-gate-blocks001010/formal-00000/build/lib/lean/ImbalancedChen');target=r/'lib/lean/ImbalancedChen';target.mkdir(parents=True,exist_ok=True)
links=[]
for p in source.rglob('*'):
 q=target/p.relative_to(source)
 if p.is_symlink():os.link(p,q,follow_symlinks=False);links.append((str(q),os.readlink(p)))
 elif p.is_dir():q.mkdir(parents=True,exist_ok=True)
 elif p.is_file():q.symlink_to(p);links.append((str(q),str(p)))
root0=Path('/workspace/p1-complete-proof/20261128-p14-parent-four-gate-block000/formal-00000/build/lib/lean/ImbalancedChen')
for ext in ['.olean','.ilean']:
 p=root0/('P5OriginalParentFourGateBlock000'+ext);q=target/p.name;q.symlink_to(p);links.append((str(q),str(p)))
def fp(p):return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest())
inputs=[fp(source/'P5OriginalParentFourGateBlocks001010.olean'),fp(root0/'P5OriginalParentFourGateBlock000.olean'),fp(f)]
cmd=['lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000',str(f)];env=os.environ.copy();env['LEAN_PATH']=str(r/'lib/lean')+os.pathsep+env.get('LEAN_PATH','');t=time.monotonic()
with (r/'probe.log').open('xb') as log:code=subprocess.run(cmd,cwd='/workspace/blue-member-build',env=env,stdout=log,stderr=subprocess.STDOUT).returncode
assert inputs==[fp(Path(x['path'])) for x in inputs]
assert all(Path(p).is_symlink() and os.readlink(p)==t for p,t in links)
result=dict(status='PASS_IMPORT_COMPATIBILITY_NO_NEW_PROOF' if code==0 else 'FAIL',exit_code=code,seconds=time.monotonic()-t,argv=cmd,inputs=inputs,log=fp(r/'probe.log'),old_normal_kernel_replay_count=0)
(r/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));raise SystemExit(code)
