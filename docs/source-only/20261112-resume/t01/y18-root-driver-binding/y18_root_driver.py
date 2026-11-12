"""Remote-only root selection/workflow/bundle binding around frozen Y18 gates.

No materializer or proof algorithm is implemented here. The reviewed candidate
remains byte-for-byte unchanged. The current proposal is deliberately blocked
until root resolves actual P2r3 shared-source/object evidence.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
HERE=Path(__file__).resolve().parent
BASE='356c3782e9428098a2fcbfb18c689bef264d84fa'
BRANCH='ci/y18-empty-mother-20261112'
CANDIDATE='docs/source-only/20261112-resume/t01/y18-validation-candidate'
DRIVER='docs/source-only/20261112-resume/t01/y18-root-driver-binding'
SELECTION='verification/parts/p0/Y18_EMPTY_MOTHER_DRIVER_SELECTION.json'
DECISION='verification/parts/p0/Y18_P2R3_REUSE_DECISION.json'
WORKFLOW='.github/workflows/y18-empty-mother-validation.yml'
CANDIDATE_REG='ad2f974d49c24296cd2f7fd079d78e60c56dcc5aa96180064b1ef4289b8f7568'
MANIFEST='8c48f34f4479b13cb38749360df78ed06f1d80ddee646472579ad0f1e214a496'
SOURCE='794fe55a2136e8f502eae426095631f64f596f7f'
HISTORICAL='f1bcf37b6fe3f0a5a4b6c4c48b166a6119f9f784'
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def checked(data,record):
 assert len(data)==record['bytes'] and sha(data)==record['sha256']
 if record.get('git_blob_sha1',record.get('git_blob')):assert raw(data)==record.get('git_blob_sha1',record.get('git_blob'))
 return data
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def file_record(path,relative):
 b=path.read_bytes();return {'path':relative,'bytes':len(b),'sha256':sha(b),'git_blob_sha1':raw(b)}
def output_roots(workspace):
 temp=Path(os.environ['RUNNER_TEMP']).resolve()
 return {'PROJECT':str(workspace/'y18-candidate'),'Y18_SOURCE_VIEW':str(temp/'y18-empty-mother-source-view'),'LOGS':str(temp/'y18-empty-mother-evidence'),'CHECKPOINT':str(temp/'y18-empty-mother-checkpoint'),'Y18_ORIGINS':str(temp/'y18-empty-mother-evidence/ORIGINS.json')}
def bind():
 assert os.environ.get('GITHUB_ACTIONS')=='true','Root-authorized GitHub driver only'
 workspace=Path(os.environ['GITHUB_WORKSPACE']).resolve();commit=os.environ['GITHUB_SHA']
 assert os.environ['PYTHONDONTWRITEBYTECODE']=='1'
 assert os.environ['SOURCE_COMMIT']==SOURCE and os.environ['HISTORICAL_COMMIT']==HISTORICAL and os.environ['EXPECTED_MANIFEST']==MANIFEST
 assert os.environ['Y18_BUNDLE']==CANDIDATE and os.environ['Y18_DRIVER']==DRIVER
 assert os.environ['Y18_MANIFEST']==str(workspace/CANDIDATE/'Y18_MANIFEST.json')
 assert all(os.environ.get(k)==v for k,v in output_roots(workspace).items())
 proof_started=int(os.environ['Y18_PROOF_STARTED_UNIX']);proof_deadline=int(os.environ['Y18_PROOF_DEADLINE_UNIX'])
 assert proof_started>0 and proof_deadline-proof_started==285*60
 assert re.fullmatch('[0-9a-f]{40}',commit)
 git=['git','-C',str(workspace)]
 assert subprocess.check_output(git+['rev-parse','HEAD'],text=True).strip()==commit
 assert not subprocess.check_output(git+['diff','HEAD','--'])
 assert os.environ['GITHUB_EVENT_NAME']=='push' and os.environ['GITHUB_REF']=='refs/heads/'+BRANCH
 raw_commit=subprocess.check_output(git+['cat-file','commit',commit]);headers=raw_commit.split(b'\n\n',1)[0].decode().splitlines()
 parents=[s.removeprefix('parent ') for s in headers if s.startswith('parent ')]
 assert parents==[BASE],'Driver must directly extend the independently reviewed immutable base'
 def committed(path,record=None):
  p=workspace/path;assert not p.is_symlink() and p.resolve().is_relative_to(workspace)
  b=p.read_bytes();assert b==subprocess.check_output(git+['show',commit+':'+path])
  if record is not None:checked(b,record)
  return b
 selection_bytes=committed(SELECTION);s=json.loads(selection_bytes)
 assert s['schema']=='y18-empty-mother-root-driver-selection-v1'
 assert (s['driver_base'],s['driver_branch'],s['workflow_path'],s['driver_bundle_path'],s['candidate_bundle_path'])==(BASE,BRANCH,WORKFLOW,DRIVER,CANDIDATE)
 assert (s['candidate_registry_sha256'],s['manifest_sha256'],s['source_commit'],s['historical_assembly'])==(CANDIDATE_REG,MANIFEST,SOURCE,HISTORICAL)
 assert s['candidate_author_allowlist_role']=='review-only-not-runtime-installed'
 assert s['original_math_scope']=={'project':337,'research':460,'strict_math':797,'built_audit_wrappers':1,'fresh_checker':798,'canonical_external':888}
 assert s['output_prefixes']=={'project':'y18-candidate','logs':'y18-empty-mother-evidence','checkpoint':'y18-empty-mother-checkpoint','source_view':'y18-empty-mother-source-view'}
 assert HERE.resolve()==(workspace/DRIVER).resolve()
 driver_registry_bytes=committed(DRIVER+'/REGISTRY.json');assert sha(driver_registry_bytes)==s['driver_registry_sha256']
 dreg=json.loads(driver_registry_bytes)
 candidate_registry_bytes=committed(CANDIDATE+'/REGISTRY.json');assert sha(candidate_registry_bytes)==CANDIDATE_REG
 creg=json.loads(candidate_registry_bytes);assert len(creg['files'])==34
 candidate_rows=[];driver_rows=[]
 for label,prefix,reg,out in [('candidate',CANDIDATE,creg,candidate_rows),('driver',DRIVER,dreg,driver_rows)]:
  records=reg['files'];assert len(records)==len({r['path'] for r in records})
  for r in records:
   path=prefix+'/'+r['path'];b=committed(path,r);out.append(file_record(workspace/path,path))
  out.append(file_record(workspace/(prefix+'/REGISTRY.json'),prefix+'/REGISTRY.json'))
  expected={r['path'] for r in out}
  actual={p.relative_to(workspace).as_posix() for p in (workspace/prefix).rglob('*') if p.is_file()}
  assert actual==expected,(label,'Unreviewed/missing payload',sorted(actual^expected))
 assert candidate_rows==s['candidate_payload'] and driver_rows==s['driver_payload']
 manifest=json.loads(committed(CANDIDATE+'/Y18_MANIFEST.json'));assert sha((workspace/CANDIDATE/'Y18_MANIFEST.json').read_bytes())==MANIFEST
 assert manifest['source_commit']==SOURCE and manifest['historical_assembly']==HISTORICAL
 audit=read(HERE/'DRIVER_BASE_WORKFLOW_AUDIT.json')
 expected={r['path']:r['expected_driver'] for r in audit['original_workflows']}
 expected[WORKFLOW]=next(r for r in dreg['files'] if r['path']=='y18-empty-mother-validation.yml')
 actual={p.relative_to(workspace).as_posix() for ext in ['*.yml','*.yaml'] for p in (workspace/'.github/workflows').glob(ext)}
 assert actual==set(expected),'All and only the reviewed eight workflows must exist'
 workflows=[]
 for path,r in sorted(expected.items()):
  committed(path,r);workflows.append(file_record(workspace/path,path))
 assert workflows==s['actual_workflow_payload']
 # The actual commit changes only these reviewed payloads, one workflow, the
 # single VE ignore addition, external selection and the eventual root decision.
 changed=set(subprocess.check_output(git+['diff-tree','--no-commit-id','--name-only','-r',BASE,commit],text=True).splitlines())
 required={r['path'] for r in candidate_rows+driver_rows}|{SELECTION,WORKFLOW,'.github/workflows/variable-envelope.yml'}
 allowed=required|{DECISION}
 assert required<=changed<=allowed,('Unexpected/missing actual driver tree delta',sorted(changed-required),sorted(required-changed))
 binding={'schema':'Y18_ACTUAL_ROOT_DRIVER_BINDING_V1','status':'PASS_ACTUAL_COMMITTED_ROOT_DRIVER_WORKFLOWS','driver_commit':commit,'actual_commit_parents':parents,'manifest_sha256':MANIFEST,'bundle_registry_sha256':CANDIDATE_REG,'driver_registry_sha256':s['driver_registry_sha256'],'source_commit':SOURCE,'historical_assembly':HISTORICAL,'selection_path':SELECTION,'selection_sha256':sha(selection_bytes),'selection_git_blob_sha1':raw(selection_bytes),'root_selection_outside_bundle_hash':True,'workflow_bindings':workflows,'candidate_payload':candidate_rows,'driver_payload':driver_rows,'actual_tree_delta':sorted(changed),'event':os.environ['GITHUB_EVENT_NAME'],'ref':os.environ['GITHUB_REF'],'output_roots':output_roots(workspace),'proof_deadline':{'started_unix':proof_started,'deadline_unix':proof_deadline,'absolute_budget_minutes':285,'job_timeout_minutes':360,'reserved_tail_minutes':75},'compiled':False,'kernel_verified':False}
 return workspace,s,binding
def authorize(workspace,selection,binding):
 # No speculative reuse/fresh-build decision is made by this proposal. A root
 # decision with actual evidence is required; coherent usable objects would
 # require a separately reviewed candidate protocol rather than an override.
 assert selection['deployment_authorized'] is True,'ROOT_DECISION_OPEN: current P2r3/shared-object decision has not been adopted'
 decision=selection['reuse_decision'];assert decision and decision['path']==DECISION
 p=workspace/DECISION;b=p.read_bytes();checked(b,decision)
 assert b==subprocess.check_output(['git','-C',str(workspace),'show',os.environ['GITHUB_SHA']+':'+DECISION])
 d=json.loads(b);assert d['status']=='ROOT_RESOLVED_NO_RELIABLE_SAME_PROFILE_SHARED_OBJECTS_AVAILABLE'
 assert d['candidate_registry_sha256']==CANDIDATE_REG and d['manifest_sha256']==MANIFEST
 assert d['candidate_protocol_unchanged'] is True and d['source_repairs_touching_this_selection']==[]
 shared=read(HERE/'P2_SHARED_SOURCE_AND_REUSE_OPEN.json')
 assert d['shared_project_modules']==shared['shared_module_names'] and d['usable_accepted_objects_restored']==[]
 assert d['evidence'] and all(re.fullmatch('[0-9a-f]{64}',r['sha256']) and r.get('origin') and r.get('role') for r in d['evidence'])
 binding['root_P2r3_shared_source_object_decision']={'path':DECISION,'sha256':sha(b),'decision':d}
 return binding
def main():
 assert len(sys.argv)==2 and sys.argv[1] in ['select','origins','verify'];mode=sys.argv[1]
 workspace,selection,binding=bind();roots=output_roots(workspace);logs=Path(roots['LOGS']);logs.mkdir(parents=True,exist_ok=True)
 if mode=='select':
  pending=logs/'DRIVER_PROPOSAL_BINDING.json';assert not pending.exists();pending.write_text(json.dumps(binding,indent=2)+'\n')
  binding=authorize(workspace,selection,binding)
  (logs/'DRIVER_BINDING.json').write_text(json.dumps(binding,indent=2)+'\n')
  for k,v in roots.items():print(k+'='+v)
  return
 binding=authorize(workspace,selection,binding);assert read(logs/'DRIVER_BINDING.json')==binding
 if mode=='origins':
  origins={HISTORICAL:str(workspace/'y18-historical-source'),SOURCE:str(workspace/'y18-published-source')}
  for ref,path in origins.items():
   assert subprocess.check_output(['git','-C',path,'rev-parse','HEAD'],text=True).strip()==ref
   assert not subprocess.check_output(['git','-C',path,'diff','HEAD','--'])
  out=Path(roots['Y18_ORIGINS']);assert not out.exists();out.write_text(json.dumps(origins,indent=2)+'\n')
 else:
  (logs/'ROOT_DRIVER_POST_BINDING.json').write_text(json.dumps(binding,indent=2)+'\n')
if __name__=='__main__':main()
