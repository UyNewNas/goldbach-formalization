"""Static metadata erratum only. Never executes the referenced stage program."""
from pathlib import Path
import ast,copy,hashlib,json
BASE=Path('E:/timot/Documents/FilesForGPT/Myath');HERE=Path(__file__).resolve().parent
OLD=BASE/'output/resume-20261112/t01/fine-winner-postimage-selection-plan'
FP=BASE/'output/resume-20261112/t01/density-validation-v2/DENSITY_MANIFEST.json'
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):(HERE/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def ident(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
source=OLD/'PROPOSED_FINE_WINNER_SOURCE_SELECTION.json';old=load(source);m=copy.deepcopy(old)
fine=load(FP);fine_rows={r['module']:r for r in fine['files']};rows={r['module']:r for r in m['files']}
changes=[]
for n,r in rows.items():
 if n.startswith('ImbalancedChen.Data.P5SubdivisionStoredBlock'):
  assert r['pre_input']['sha256']==fine_rows[n]['sha256']
  assert 'origin' not in r['pre_input']
  r['pre_input']['origin']=copy.deepcopy(fine_rows[n]['origin'])
  changes.append({'module':n,'added_pre_input_origin':r['pre_input']['origin'],'pre_input_sha256':r['pre_input']['sha256'],'selected_source_sha256_unchanged':r['sha256']})
assert len(changes)==72

def pairs_identity(rs,names):
 data=[[n,rs[n]['sha256']] for n in sorted(names)]
 return sha(json.dumps(data,ensure_ascii=True,separators=(',',':')).encode())
def triples_identity(rs,names):
 data=[[n,rs[n]['sha256'],rs[n]['git_blob_sha1']] for n in sorted(names)]
 return sha(json.dumps(data,ensure_ascii=True,separators=(',',':')).encode())
old_fine_id=fine['targets'][0]['source_identity_sha256']
assert pairs_identity(fine_rows,fine_rows)==old_fine_id
fine_target=fine['targets'][0]['primary_module']
target_names=[fine_target]+[t for t in old['targets'] if isinstance(t,str)]
assert len(target_names)==9 and len(set(target_names))==9
def target_record(t):
 seen=set();external=set();stack=[];order=[]
 def visit(n):
  if not n.startswith('ImbalancedChen.'):external.add(n);return
  assert n in rows,('missing',n)
  assert n not in stack,('cycle',n)
  if n in seen:return
  stack.append(n)
  for im in rows[n]['imports']:visit(im)
  stack.pop();seen.add(n);order.append(n)
 visit(t)
 return {'primary_module':t,'closure_modules':sorted(seen),'external_imports':sorted(external),'unresolved_modules':[],'source_identity_sha256':pairs_identity(rows,seen),'source_and_git_blob_identity_sha256':triples_identity(rows,seen)}
targets=[target_record(t) for t in target_names]
assert len(targets[0]['closure_modules'])==1808
assert targets[0]['source_identity_sha256']=='cbfab9b665a35824f1215eb96a19d0dcf4490471d8a462c0147c309191a27b71'
assert targets[0]['source_and_git_blob_identity_sha256']=='643ec0de6be762f54d44c92ca78ef02b374bfcbb0980fd487673119c8de2f91b'
assert set().union(*(set(t['closure_modules']) for t in targets))==set(rows)
m['targets']=targets
m['source_identity_sha256']=pairs_identity(rows,rows)
m['source_identity_recipe']="SHA256(UTF8(json.dumps([[module,sha256] for module in sorted(selected_project_module_names)],ensure_ascii=True,separators=(',',':')))); no trailing newline. Per-target identities use exactly that target's actual DFS project closure."
m['source_and_git_blob_identity_sha256']=old['source_identity_sha256']
assert m['source_and_git_blob_identity_sha256']==triples_identity(rows,rows)
m['source_and_git_blob_identity_recipe']=old['source_identity_recipe']
m['historical_metadata']={'original_frozen_proposal':ident(source),'original_proposal_project_triple_identity_sha256':old['source_identity_sha256'],'old_Fine_original_source_identity_sha256':old_fine_id,'old_Fine_manifest':ident(FP),'old_Fine_identity_status':'HISTORICAL_ONLY; this describes the unrevised Fine selection, not any successor target.'}
m['schema']='T01_FINE_WINNER_PROPOSED_SUCCESSOR_SOURCE_SELECTION_METADATA_ERRATA_V1'
m['metadata_erratum_only']=True;m['driver_ready']=False

# Confirm that only metadata changed: no original/postimage, transform,
# imports, public type or 071 source byte is modified by this correction.
old_rows={r['module']:r for r in old['files']}
for n,r in rows.items():
 normalized=copy.deepcopy(r)
 if n in {c['module'] for c in changes}:normalized['pre_input'].pop('origin')
 assert normalized==old_rows[n]
keys=set(targets[0]);assert all(set(t)==keys for t in targets)
assert all(t['source_identity_sha256']!=old_fine_id for t in targets)
dump('PROPOSED_FINE_WINNER_SOURCE_SELECTION.stage-corrected.json',m)
dump('METADATA_DELTA.json',{'status':'STATIC_ERRATUM_ORIGINAL_FREEZE_UNCHANGED','original':ident(source),'pre_input_origin_additions':changes,'historical_Fine_identity':old_fine_id,'actual_target_identities':[{'primary_module':t['primary_module'],'closure_count':len(t['closure_modules']),'source_identity_sha256':t['source_identity_sha256'],'source_and_git_blob_identity_sha256':t['source_and_git_blob_identity_sha256']} for t in targets],'actual_project_union_count':len(rows),'actual_project_pair_identity_sha256':m['source_identity_sha256'],'existing_project_triple_identity_sha256':m['source_and_git_blob_identity_sha256'],'uniform_target_schema':sorted(keys),'source_and_transform_bytes_changed':False,'stage_executed':False,'existing_stage_hardcoded_scope_not_modified':True})
dump('STATIC_CHECKS.json',{'Python_AST':bool(ast.parse(Path(__file__).read_text(encoding='utf-8'))),'72_pre_input_origins_complete':all(all(k in r['pre_input'] for k in ['origin','bytes','sha256','git_blob_sha1']) for n,r in rows.items() if n.startswith('ImbalancedChen.Data.P5SubdivisionStoredBlock')),'9_uniform_actual_target_records':len(targets)==9 and all(set(t)==keys for t in targets),'Fine_actual_DFS':len(targets[0]['closure_modules']),'all_target_closures_union1816':len(set().union(*(set(t['closure_modules']) for t in targets)))==1816,'old_efca_only_historical':all(t['source_identity_sha256']!=old_fine_id for t in targets),'source_and_transform_payloads_unchanged':True,'materializer_not_executed':True})
print(json.dumps({'added_pre_origins':len(changes),'target_identities':[{'module':t['primary_module'],'count':len(t['closure_modules']),'sha256':t['source_identity_sha256']} for t in targets],'union_source_identity':m['source_identity_sha256']},indent=2))
