"""Remote-only same-environment canonical-object join for actual final consumers.

This is not a compiler/checker replacement. It records the ordered LEAN_PATH,
joins the first existing selected public object to its actual canonical build
path/hash, then runs only the original guarded lean/leanchecker in that very
environment and cwd. No project/native aliases or warm-cache claims are allowed.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
HERE=Path(__file__).resolve().parent
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,r):
 assert not p.exists();p.write_text(json.dumps(r,indent=2)+'\n')
def main():
 assert os.environ.get('GITHUB_ACTIONS')=='true','Root-authorized remote consumer only'
 assert len(sys.argv)==2 and sys.argv[1] in ['wrapper','checker','audit'];mode=sys.argv[1]
 manifest=HERE/'Y18_MANIFEST.json';assert sha(manifest)==os.environ['EXPECTED_MANIFEST'];m=json.loads(manifest.read_text())
 project=Path(os.environ['PROJECT']).resolve();logs=Path(os.environ['LOGS']);assert Path.cwd().resolve()==project
 lean_path=os.environ.get('LEAN_PATH');assert lean_path is not None and lean_path!='','Must execute via actual lake env'
 raw_parts=lean_path.split(os.pathsep);assert all(raw_parts),'Empty implicit search entries are not authorized'
 roots=[(project/Path(p)).resolve() if not Path(p).is_absolute() else Path(p).resolve() for p in raw_parts]
 expected={r['module']:(project/'.lake/build/lib/lean'/Path(*r['module'].split('.'))).with_suffix('.olean') for r in m['files']}
 expected.update({r['module']:(project/'.lake/packages/goldbach/.lake/build/lib/lean'/Path(*r['module'].split('.'))).with_suffix('.olean') for r in m['all_native_sources']})
 if mode!='wrapper':expected['CandidateAudit']=project/'.lake/build/lib/lean/CandidateAudit.olean'
 def resolve():
  rows=[]
  for name,canonical in sorted(expected.items()):
   rel=Path(*name.split('.')).with_suffix('.olean');found=[r/rel for r in roots if (r/rel).is_file()]
   assert found,('No actual LEAN_PATH object',name)
   first=found[0];assert not first.is_symlink() and first.resolve()==canonical.resolve(),('Selected consumer loads a shadow object',name,str(first),str(canonical))
   assert canonical.stat().st_size>0
   rows.append({'module':name,'first_actual_path':str(first.resolve()),'canonical_path':str(canonical.resolve()),'bytes':canonical.stat().st_size,'sha256':sha(canonical),'all_found_paths':[str(p.resolve()) for p in found]})
  return rows
 explicit=m['compiler_profiles']['wrapper']['explicit_args']
 if mode=='checker':command=['leanchecker','--verbose',*m['fresh_kernel_modules']]
 elif mode=='audit':command=['lean',*explicit,'CandidateAudit.lean']
 else:
  (project/'.lake/build/lib/lean').mkdir(parents=True,exist_ok=True);(project/'.lake/build/ir').mkdir(parents=True,exist_ok=True)
  command=['lean',*explicit,'-o','.lake/build/lib/lean/CandidateAudit.olean','-i','.lake/build/lib/lean/CandidateAudit.ilean','-c','.lake/build/ir/CandidateAudit.c','CandidateAudit.lean']
 state_path=Path(os.environ['P0_CI_GUARD_STATE']);state=json.loads(state_path.read_text())
 assert state_path.resolve()==(logs/'runtime/state.json').resolve() and state['root']==str(project)
 assert state['guard_sha256']==m['runtime_reuse']['sha256']
 assert all(os.environ.get(k)==v for k,v in state['environment'].items())
 tool=command[0];executable=Path(state['shadow'])/'bin'/tool
 assert shutil.which(tool)==str(executable),'Actual consumer PATH bypasses pinned guard/runtime'
 def executable_binding():
  if tool=='leanchecker':
   real=Path(state['realbin'])/'leanchecker'
   assert executable.is_symlink() and executable.resolve()==real.resolve()
   assert sha(executable)==sha(real)==state['runtime_sha256'][str(real)]
   return [{'path':str(executable),'resolved_path':str(executable.resolve()),'sha256':sha(executable),'runtime_identity_key':str(real)}]
  assert tool=='lean' and not executable.is_symlink()
  runtime=Path(state['shadow'])/'bin/lean-runtime';real=Path(state['realbin'])/'lean'
  assert sha(executable)==state['runtime_sha256'][str(executable)]
  assert sha(runtime)==state['runtime_sha256'][str(runtime)]==state['runtime_sha256'][str(real)]==sha(real)
  return [{'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'runtime_identity_key':str(p)} for p in [executable,runtime,real]]
 actual_tools=executable_binding();command[0]=str(executable)
 pre={'schema':'Y18_ACTUAL_CONSUMER_SOURCE_OBJECT_JOIN_V1','consumer':mode,'manifest_sha256':sha(manifest),'driver_commit':os.environ['GITHUB_SHA'],'source_commit':m['source_commit'],'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'cwd':str(project),'raw_LEAN_PATH':lean_path,'ordered_lean_path':[str(p) for p in roots],'LEAN_SYSROOT':os.environ.get('LEAN_SYSROOT'),'resolved_command_executable':str(executable),'runtime_state_sha256':sha(state_path),'actual_tool_runtime_bindings':actual_tools,'command':command,'selected_public_objects':resolve(),'cache_alias_accepted':False,'kernel_acceptance_claim':False}
 write(logs/('CONSUMER_'+mode+'_PRE.json'),pre)
 result=subprocess.run(command,env=os.environ.copy(),check=False)
 assert executable_binding()==actual_tools and sha(state_path)==pre['runtime_state_sha256']
 post={**pre,'returncode':result.returncode,'selected_public_objects':resolve()}
 assert post['selected_public_objects']==pre['selected_public_objects'],'Consumed objects changed during actual consumer'
 post['status']='PASS_SAME_ENV_CANONICAL_OBJECTS_AND_ACTUAL_CONSUMER_EXIT' if result.returncode==0 else 'ACTUAL_CONSUMER_REJECTED'
 write(logs/('CONSUMER_'+mode+'_POST.json'),post)
 if result.returncode:raise SystemExit(result.returncode)
if __name__=='__main__':main()
