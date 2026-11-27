python3 -B - <<'PY'
from pathlib import Path
import hashlib,json,subprocess,sys
if not __debug__: raise RuntimeError('assertions required')
sys.dont_write_bytecode=True
repo=Path('/workspace/goldbach-formalization')
project=Path('/workspace/blue-member-build')
source='a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52'
driver_path='docs/p1/20261125/p14-continuation/run_stage.py'
driver_sha='a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1'
root=Path('/workspace/p1-complete-proof/20261125-p14-continuation')
bootstrap=Path('/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap')/source/'restored-p1-three-singletons'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(path):return subprocess.check_output(['git','show',source+':'+path],cwd=repo)
def frozen(path,data):
 path.parent.mkdir(parents=True,exist_ok=True)
 if path.exists():assert path.is_file() and path.read_bytes()==data, str(path)
 else:
  with path.open('xb') as f:f.write(data)
def read_pin(path,digest,size=None):
 p=Path(path);assert all(not x.is_symlink() for x in (p,*p.parents)),path
 data=p.read_bytes();assert sha(data)==digest,path
 assert size is None or len(data)==size,path
 return data
specs=[{'stage': 'child-gap-expression-retry', 'manifest': 'docs/p1/20261125/p14-continuation/stages/child-gap-expression-retry.json', 'manifest_sha256': 'e9ffb4e403e81ebe509765409d0abbf712765325c452b559fca981b932881838', 'target': {'after_sha256': '8ab2b85ae8dbbdef067ff12e439a24e248bc08efeafabdd7f3df69abf744be69', 'before_sha256': '709220f1d167d2abb8962e18c9a101206099ae73e77cea5749273fa3852995b8', 'module': 'ImbalancedChen.P5OldFifthChildGapIntegral', 'path': 'ImbalancedChen/P5OldFifthChildGapIntegral.lean', 'preimage_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4'}, 'prerequisite': {'pipeline_path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json', 'pipeline_raw_sha256': 'a9e670f74bee98fd8a65ba3ea6de824a804fbcb1b5cffe8782a88463b755be61', 'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4/runs/attempt-00000/RESULT.json', 'result_raw_sha256': '1bd8ef938e3fec3ff550a6d79828923699db05d9c026284749d797c4d9cd42e7', 'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4', 'source_sha256': '3777f1200e46cf909cac65802868b9fbadcbfb00dd70e77428013e83eb7b4728', 'stage': 'barycentric-id-power-retry', 'target_module': 'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric', 'result_raw_bytes': 1050, 'pipeline_raw_bytes': 7339}}, {'stage': 'uniform-adopted-error-add-cast-retry', 'manifest': 'docs/p1/20261125/p14-continuation/stages/uniform-adopted-error-add-cast-retry.json', 'manifest_sha256': '1a9245dcc1ca6955e40b02f3f6592f9b65e213866d74a50a70e42a6f7d554dcc', 'target': {'after_sha256': '1c194e52f20b7d5ab65038c8b467b57a38e29d3d36e033775a0b5aaca882b8f0', 'before_sha256': '5c0012206c93e05871ead313c5e410217e751073f81e76b3abf6c2806c59973d', 'module': 'ImbalancedChen.P1OriginalFifthUniformAdoptedBankError', 'path': 'ImbalancedChen/P1OriginalFifthUniformAdoptedBankError.lean', 'preimage_commit': '14845975a892974d2633c283f73f03cb87faae27'}, 'prerequisite': {'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/runs/attempt-00000/RESULT.json', 'result_raw_sha256': '1092a877b78475b016368ae49f314938092b38d32eb94d8d5e34b8841c4493f8', 'source_commit': '14845975a892974d2633c283f73f03cb87faae27', 'source_sha256': '3d326d98699f1d6b99290e20fbd50bdfbd08de0bda20a8a64dd1bab8ff6eec69', 'stage': 'adopted-owner-bank-typed-bound-retry', 'target_module': 'ImbalancedChen.P1OriginalFifthAdoptedOwnerBank', 'result_raw_bytes': 1048}}, {'stage': 'typed-key-uniqueness-kernel-exception-diagnostic', 'manifest': 'docs/p1/20261125/p14-continuation/stages/typed-key-uniqueness-kernel-exception-diagnostic.json', 'manifest_sha256': 'c428e0a1e0ca261489d3d60e1f4e455e0c38fa46b400b31e334a7f37a2cc1ef7', 'target': {'after_sha256': '7b1a664fca62612a8f2d198a15e512420bb853a2d155eddf7950cec05660973b', 'before_sha256': '8204516c6c83ad76e08faf0e9a2ab5a7519075ca96473f94da664dbe47ea157d', 'module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate', 'path': 'ImbalancedChen/P1HistoricalFifthTypedKeyUniquenessCertificate.lean', 'preimage_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5'}, 'prerequisite': {'pipeline_path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/504f9546a9d919ed1977c396517d5838ffd0284c/typed-key-uniqueness/PIPELINE_RESULT.json', 'pipeline_raw_bytes': 996, 'pipeline_raw_sha256': '6a7f93437ebe3d802360af8993fd513b5e9a8c028e63d9d854b83247e57d758f', 'result_path': '/workspace/p1-complete-proof/20261125-p14-continuation/typed-key-uniqueness-core/504f9546a9d919ed1977c396517d5838ffd0284c/runs/attempt-00000/RESULT.json', 'result_raw_bytes': 1061, 'result_raw_sha256': 'ea85ed439655b1a7ad20f4932831abe4c5a71ed2ce81f0a3f92f8cdc2b424388', 'source_commit': '504f9546a9d919ed1977c396517d5838ffd0284c', 'source_sha256': 'f475f4f9f11b339883b2ee6e09db226cb437803df1f574fdb0717f702a7809ac', 'stage': 'typed-key-uniqueness-core', 'target_module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore'}}]
protected={'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb', 'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03', 'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377', 'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51'}
subprocess.run(['git','fetch','origin','refs/heads/codex/p1-4-continuation-20261125'],cwd=repo,check=True)
driver=git(driver_path);assert sha(driver)==driver_sha
out=bootstrap/'PIPELINE_RESULT.json'
assert not out.exists(),'existing final pipeline must be inspected and reused'
reused=[]
for s in specs:
 t=s['target'];p=s['prerequisite']
 data=git(s['manifest']);assert sha(data)==s['manifest_sha256']
 manifest=json.loads(data);assert manifest['stage']==s['stage'] and manifest['modules']==[t]
 assert sha(git(t['path']))==t['after_sha256']
 target=project/t['path'];assert target.is_file() and sha(target.read_bytes()) in (t['before_sha256'],t['after_sha256'])
 previous=list((root/s['stage']/source/'runs').glob('attempt-*'))
 assert not previous,'existing candidate run must be inspected, not repeated: '+s['stage']
 data=read_pin(p['result_path'],p['result_raw_sha256'],p['result_raw_bytes']);old=json.loads(data)
 assert old['source_commit']==p['source_commit'] and old['stage']==p['stage']
 assert old['accepted_owners']==old['normal_passed']==[p['target_module']]
 assert old['normal_failed_or_held']=={} and old['audit_error'] is None
 assert old['targets']=={p['target_module']:p['source_sha256']}
 assert old['whole_P1_4_complete'] is False and old['protected_roots']==protected
 assert sha((project/(p['target_module'].replace('.','/')+'.lean')).read_bytes())==p['source_sha256']
 if 'pipeline_path' in p:
  prior=json.loads(read_pin(p['pipeline_path'],p['pipeline_raw_sha256'],p['pipeline_raw_bytes']))
  assert prior['source_commit']==p['source_commit'] and prior['whole_P1_4_complete'] is False
  assert prior['accepted_owners']==[p['target_module']]
  joined=[r for r in prior['stages'] if r['stage']==p['stage']]
  assert len(joined)==1 and joined[0]['accepted_owners']==[p['target_module']] and joined[0]['exit_code']==0
  assert joined[0]['result_path']==p['result_path']
 reused.append(p)
bootstrap.mkdir(parents=True,exist_ok=True)
executed=bootstrap/'run_stage.py';frozen(executed,driver)
frozen(bootstrap/'CANDIDATE_BINDING.json',json.dumps({'source_commit':source,'specs':specs,'whole_P1_4_complete':False},indent=2,sort_keys=True).encode())
checks=[]
for s in specs:
 cmd=['python3','-B',str(executed),'--source-commit',source,'--manifest',s['manifest'],'--check']
 proc=subprocess.run(cmd,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 frozen(bootstrap/'checks'/(s['stage']+'.log'),proc.stdout)
 print(proc.stdout.decode('utf-8',errors='replace'),flush=True)
 assert proc.returncode==0,'read-only closure check failed: '+s['stage']
 obj=json.loads(proc.stdout);assert obj['status']=='READ_ONLY_SOURCE_CHECK_PASS_NOT_ACCEPTANCE'
 assert obj['source_commit']==source and obj['targets']==[s['target']['module']] and obj['protected_roots']==protected
 checks.append({'stage':s['stage'],'exit_code':0,'log_sha256':sha(proc.stdout),'source_closure_count':obj['source_closure_count']})
results=[];accepted=set()
for s in specs:
 proc=subprocess.run(['python3','-B',str(executed),'--source-commit',source,'--manifest',s['manifest'],'--run'],cwd=repo)
 candidates=sorted((root/s['stage']/source/'runs').glob('attempt-*/RESULT.json'))
 row={'stage':s['stage'],'exit_code':proc.returncode,'accepted_owners':[]}
 if candidates:
  assert len(candidates)==1,'unexpected multiple candidate results'
  raw=candidates[0].read_bytes();result=json.loads(raw)
  assert result['source_commit']==source and result['stage']==s['stage'] and result['whole_P1_4_complete'] is False
  assert result['targets']=={s['target']['module']:s['target']['after_sha256']} and result['protected_roots']==protected
  assert set(result['accepted_owners']) <= {s['target']['module']}
  if result['accepted_owners']:
   assert proc.returncode==0 and result['normal_passed']==[s['target']['module']] and result['normal_failed_or_held']=={} and result['audit_error'] is None
  row.update(result_path=str(candidates[0]),result_sha256=sha(raw),accepted_owners=result['accepted_owners'])
  accepted.update(result['accepted_owners'])
 else:row['status']='HELD_NO_STAGE_RESULT'
 results.append(row);print(json.dumps({'pipeline_stage_result':row}),flush=True)
report={'source_commit':source,'driver_sha256':driver_sha,'checks':checks,'reused_original_stage_results':reused,'stages':results,'accepted_owners':sorted(accepted),'whole_P1_4_complete':False}
frozen(out,json.dumps(report,indent=2,sort_keys=True).encode());print(json.dumps(report),flush=True)
raise SystemExit(0 if all(r['exit_code']==0 and r['accepted_owners'] for r in results) else 1)
PY
