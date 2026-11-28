"""Publish this sealed owner via exact Git blob parts; no proof command or proof-output edit."""
from pathlib import Path
import json,hashlib,subprocess,shutil,sys,datetime
if not __debug__:
 raise SystemExit('Integrity checks require Python without -O/PYTHONOPTIMIZE')
TRANSPORT=Path(__file__).resolve().parent
ROOT=Path('/workspace/p1-complete-proof/20261128-p15-saved-sixth-archive')
mode=sys.argv[1];assert mode in ['p15','p14']
WORK=Path('/workspace/p15-continue-20261127' if mode=='p15' else '/workspace/p14-continue-20261128')
BRANCH='work/p1-5-actual-means-20261125' if mode=='p15' else 'codex/p1-4-continuation-20261125'
EXPECTED='05744e06ee17c832ed872fb2340ef28d91af494d' if mode=='p15' else '1b3cfa3aee1c45202305c9f39102681467d2ee93'
SLUG=mode+'-saved-sixth-archive';DOCS_REL='docs/p1/20261128/'+SLUG
PART_BYTES=45*1024*1024

def git(*args,text=True,input=None):return subprocess.check_output(['git',*args],cwd=WORK,text=text,input=input)
def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(p):return hashlib.file_digest(Path(p).open('rb'),'sha256').hexdigest()
def save(p,data):Path(p).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')

assert not git('status','--porcelain') and git('rev-parse','HEAD').strip()==EXPECTED
if mode=='p15':assert not (ROOT/'PUBLISHED.json').exists()
else:
 published=json.loads((ROOT/'PUBLISHED.json').read_text());assert published['source_and_archive_git_blobs_verified'] and not published.get('additional_publications')
selected=json.loads((ROOT/'ACCEPTED_ATTEMPT.json').read_text());FINAL=ROOT/selected['attempt'];result=json.loads((FINAL/'VALIDATION_RESULTS.json').read_text())
assert result['status']=='PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED' and result['owned']==145 and result['private']==108
assert json.loads((FINAL/'LANE.json').read_text())['exit_code']==0 and json.loads((FINAL/'COUPLED_IMPORT_VALIDATION.json').read_text())['status']=='PASS'
review=json.loads((ROOT/'INDEPENDENT_REVIEW.json').read_text());assert review['blocking_findings']==[] and review['source_sha256']==result['source']['sha256']
assert file_sha(FINAL/'EXECUTED_DRIVER.py')==review['driver_sha256']
meta=json.loads((ROOT/'ARCHIVE.json').read_text());archive=ROOT/meta['archive'];assert archive.stat().st_size==meta['bytes'] and file_sha(archive)==meta['sha256']
source=Path(result['source']['path']).read_bytes();assert sha(source)==result['source']['sha256']
rel=result['module'].replace('.','/')+'.lean';original_sha=json.loads((ROOT/'SOURCE_CHANGE_PLAN.json').read_text())['original_source_sha256'];assert sha(git('show','HEAD:'+rel,text=False))==original_sha
# Status alone may hide local changes under pre-existing index flags.
assert git('ls-files','-v','--',rel).strip()=='H '+rel, 'source has sparse/assume-unchanged flags'
assert (WORK/rel).is_file() and not (WORK/rel).is_symlink() and file_sha(WORK/rel)==original_sha, 'working source changed'
checks=[]
for row in json.loads((ROOT/'REUSED_CONTEXTS.json').read_text())+json.loads((ROOT/'ORDINARY_ACTUAL_SOURCE_CLOSURE.json').read_text())['sources']:
 h=sha(git('show','HEAD:'+row['module'].replace('.','/')+'.lean',text=False));assert h==row['source']['sha256'],row['module'];checks.append({'module':row['module'],'sha256':h})
assert len(checks)==177
# Avoid redundant physical working-tree copies of 226MiB of immutable archive parts.
# Store each exact part once in Git's shared object store, then stage sparse paths.
parts=[];whole=hashlib.sha256();offset=0
with archive.open('rb') as stream:
 for index in range((meta['bytes']+PART_BYTES-1)//PART_BYTES):
  data=stream.read(PART_BYTES);assert data
  oid=git('-c','core.compression=0','hash-object','-w','--stdin',text=False,input=data).decode().strip()
  assert git('cat-file','blob',oid,text=False)==data
  parts.append({'index':index,'file':archive.name+f'.part-{index:03d}','offset':offset,'bytes':len(data),'sha256':sha(data),'git_blob':oid})
  whole.update(data);offset+=len(data)
 assert not stream.read(1)
assert offset==meta['bytes'] and whole.hexdigest()==meta['sha256']
manifest={'schema':'P1_exact_sealed_zip_Git_parts_v1','master':{'file':archive.name,'bytes':meta['bytes'],'sha256':meta['sha256']},'part_bytes_limit':PART_BYTES,'git_directory':DOCS_REL,'parts':parts,'parts_stored_in_Git_sparse_worktree_omission_documented':True,'all_part_bytes_read_back_equal_master_ranges':True,'new_proof_commands':0,'whole_P1_4_complete':False,'whole_P1_5_complete':False}
save(TRANSPORT/(mode+'-GITHUB_PARTS.json'),manifest)
DOCS=WORK/DOCS_REL;assert not DOCS.exists();DOCS.mkdir(parents=True);(WORK/rel).write_bytes(source)
for name in ['PLAN.md','SOURCE_CHANGE_PLAN.json','SOURCE_GIT_COUPLING.json','IMPORT_GIT_BINDING.json','ORDINARY_ACTUAL_SOURCE_CLOSURE.json','ORDINARY_IMPORT_SIX_FIELDS.json','MANUSCRIPT_SCOPE.json','REUSE_SEARCH.json','OWN_INPUT_FIXTURES.json','prepare_input.py','INPUT_SETUP.md','INDEPENDENT_REVIEW.json','ACCEPTED_ATTEMPT.json','ACCEPTANCE.json','ARCHIVE.json','package_evidence.py','PERFORMANCE_OBSERVATION.json']:
 if (ROOT/name).exists():shutil.copyfile(ROOT/name,DOCS/name)
shutil.copyfile(TRANSPORT/'reassemble_evidence.py',DOCS/'reassemble_evidence.py');shutil.copyfile(__file__,DOCS/'publish_exact_parts.py');save(DOCS/'GITHUB_PARTS.json',manifest)
scope=json.loads((ROOT/'MANUSCRIPT_SCOPE.json').read_text())['mathematical_scope']
(DOCS/'README.md').write_text('# Original complete sixth NPY input and Source interface\n\n'+scope+'\n\nAccepted formal-00004:145actual-owned/108private, normal/sole-module kernel/full-owned types-Expr-universes-axioms/coupled/lane0 and independent read-only review. Complete55625280bytes,632104x11,i64/Corder/original128byte header and all217287original blocks retained.54contiguous chunks,54private lengths and a local binary length composition; all original public statements/conditions retained. No all-row geometry, coverage, numerical saving, density or global signedM/payment claim. P1.4/P1.5 remain OPEN;18/21 and three ProperPower HOLDs unchanged. Direct guarded checks, not fresh Lake import-closure acceptance.\n\nThe sealed ZIP exceeds GitHub single-file limits. Its6exact parts (each <=45MiB) are stored as Git blobs; local sparse worktrees may omit physical part files. Reassemble from any clone containing this commit:\n\n```sh\npython3 '+DOCS_REL+'/reassemble_evidence.py --repository . --output /workspace/p1-evidence/'+archive.name+'\n```\n\nGITHUB_PARTS.json binds offsets, sizes, each SHA256 and full ZIP SHA256. Reconstruction checks every part, full digest and all ZIP CRCs, without Lean. The original local master and all accepted compiler outputs are preserved. Original input setup: `python3 '+DOCS_REL+'/prepare_input.py --repository .`; see INPUT_SETUP.md.\n')
if mode=='p14':save(DOCS/'P14_SOURCE_REUSE.json',{'status':'PASS_EXACT_ACCEPTED_SOURCE_AND_MULTIPART_EVIDENCE_REUSE','p15_origin_commit':published['commit'],'p14_base_commit':EXPECTED,'source_sha256':result['source']['sha256'],'import_source_checks':checks,'same_sealed_archive_sha256':meta['sha256'],'new_normal_or_kernel_commands':0,'new_proof_credit':0,'whole_P1_4_complete':False,'whole_P1_5_complete':False})
subprocess.run(['git','add','--sparse',rel,DOCS_REL],cwd=WORK,check=True)
part_paths=[]
for part in parts:
 path=DOCS_REL+'/'+part['file'];assert not (WORK/path).exists();subprocess.run(['git','update-index','--add','--cacheinfo','100644,'+part['git_blob']+','+path],cwd=WORK,check=True);part_paths.append(path)
subprocess.run(['git','update-index','--skip-worktree',*part_paths],cwd=WORK,check=True)
subprocess.run(['git','-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=WORK,check=True)
body=TRANSPORT/(mode+'-commit.txt');body.write_text(('Seal' if mode=='p15' else 'Reuse accepted')+' original complete sixth NPY input\n\n'+scope+'\n\n145owned/108private, same normal/kernel/full-owned/coupled accepted owner, no old proof replay. Exact236732053byte sealed ZIP transported in6Git parts <=45MiB; each part read back bytewise and full archive digest retained. Parts use documented sparse index paths to preserve disk; all original compiler outputs and local master remain unchanged. P1.4/P1.5 still open;18/21 and three HOLDs unchanged.\n')
subprocess.run(['git','commit','-F',str(body)],cwd=WORK,check=True);head=git('rev-parse','HEAD').strip();save(TRANSPORT/(mode+'-STAGE.json'),{'status':'COMMITTED_BEFORE_PUSH','commit':head,'branch':BRANCH,'master_sha256':meta['sha256']})
assert sha(git('show',head+':'+rel,text=False))==result['source']['sha256']
assert git('show',head+':'+DOCS_REL+'/GITHUB_PARTS.json',text=False)==(DOCS/'GITHUB_PARTS.json').read_bytes()
expected_paths={rel,*[str(p.relative_to(WORK)) for p in DOCS.rglob('*') if p.is_file()],*part_paths}
assert set(git('diff','--name-only',EXPECTED,head).splitlines())==expected_paths
whole=hashlib.sha256();total=0
for part in parts:
 path=DOCS_REL+'/'+part['file'];assert git('rev-parse',head+':'+path).strip()==part['git_blob'];data=git('show',head+':'+path,text=False);assert len(data)==part['bytes'] and sha(data)==part['sha256'];whole.update(data);total+=len(data)
assert total==meta['bytes'] and whole.hexdigest()==meta['sha256'] and not git('status','--porcelain')
save(TRANSPORT/(mode+'-STAGE.json'),{'status':'COMMITTED_CONTENT_VERIFIED_BEFORE_PUSH','commit':head,'branch':BRANCH,'master_sha256':meta['sha256'],'source_manifest_each_part_and_whole_archive_verified':True})
subprocess.run(['git','-c','pack.window=0','-c','pack.threads=1','-c','pack.compression=0','push','origin','HEAD:'+BRANCH],cwd=WORK,check=True)
assert git('ls-remote','origin','refs/heads/'+BRANCH).split()[0]==head
if mode=='p15':published={'commit':head,'remote_branch':BRANCH,'remote_head_verified':True,'source_and_archive_git_blobs_verified':True,'archive_storage':'6exact Git parts; combined master digest verified','multipart_manifest_git_path':DOCS_REL+'/GITHUB_PARTS.json','whole_P1_4_complete':False,'whole_P1_5_complete':False}
else:published['additional_publications']=[{'commit':head,'remote_branch':BRANCH,'remote_head_source_archive_verified':True,'multipart_manifest_git_path':DOCS_REL+'/GITHUB_PARTS.json','new_proof_commands':0}]
save(ROOT/'PUBLISHED.json',published);save(TRANSPORT/(mode+'-STAGE.json'),{'status':'PUSHED_AND_VERIFIED','commit':head,'branch':BRANCH,'master_sha256':meta['sha256'],'all_parts_rehashed_and_index_skipworktree_for_storage_only':True})
print('PUBLISHED_EXACT_MULTIPART',mode,head,len(parts),meta['bytes'])
