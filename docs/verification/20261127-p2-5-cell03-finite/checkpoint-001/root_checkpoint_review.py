from pathlib import Path
import base64,collections,hashlib,json,lzma,re,subprocess,tarfile

root=Path('/workspace/scratch/674430b6afba/cell03-verify')
repo=Path('/workspace/scratch/ffd83d72c265/goldbach-formalization')
cp=root/'checkpoint-001'
def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(p.read_bytes())
delivery=read(cp/'DELIVERY_MANIFEST.json')
for n,q in delivery['deliverables'].items():
 p=cp/n;assert p.stat().st_size==q['bytes'] and sha(p.read_bytes())==q['sha256'],n
bundle=json.loads(lzma.decompress((cp/'ACTUAL_EVIDENCE_DICT64.json.xz').read_bytes()))
files={}
for n,q in bundle['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts,n
 b=base64.b64decode(q['base64'],validate=True)
 assert len(b)==q['bytes'] and sha(b)==q['sha256'],n
 files[n]=b
assert len(files)==delivery['embedded_files']==625
v=read(cp/'VERIFICATION.json');index=read(cp/'NEW_ACCEPTED_OBJECTS.json')['project_objects']
assert v['verified_checkpoint'] and v['partial_checkpoint'] and not v['accepted']
assert v['accepted_new_owner_count']==len(index)==len(v['owners'])==45
assert v['successful_stages']=={'NORMAL':45,'REPLAY':45,'AUDIT':45}
assert v['before_after_contexts_verified']==270
assert not v['P2_5_proved'] and not v['physical_geometry_proved'] and not v['all_fourteen_cell_q96_endpoint_proved']
assert v['candidate_lean_sources_modified']==v['prior_project_owners_recompiled']==0
publication='68703c066df26624af2f2d45b6e0b0a1fd365b6d'
assert v['source_publication']==publication
ep='docs/source-only/20261127-p2-5-cell03-finite/PUBLIC_EXPECTATIONS.json'
expected_raw=subprocess.check_output(['git','show',publication+':'+ep],cwd=repo)
assert sha(expected_raw)==v['public_expectations_sha256_from_original_source_commit']
expected=json.loads(expected_raw)['modules']
template=(repo/'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean').read_text()
decl_count=0;records=[]
for m,q in sorted(index.items()):
 name=m.split('.')[-1];stage='evidence/'+name+'/'
 result_raw=files[stage+'RESULT.json'];r=json.loads(result_raw)
 assert sha(result_raw)==q['result_sha256']==v['owners'][m]['result_sha256']
 assert r['accepted'] and r['module']==m and r['source_sha256']==q['source_sha256']
 source=repo/v['source_graph'][m]['path'];src=source.read_bytes()
 assert sha(src)==q['source_sha256']
 assert subprocess.check_output(['git','show',publication+':'+str(source.relative_to(repo))],cwd=repo)==src
 assert re.findall(r'^import (ImbalancedChen\.\w+)',src.decode(),re.M)==q['direct_project_imports']
 stages=json.loads(files[stage+'STAGES.json'])
 assert [(x['stage'],x['exit_code']) for x in stages]==[('NORMAL',0),('REPLAY',0),('AUDIT',0)]
 assert all(x['log_sha256']==sha(files[stage+x['stage']+'.log']) for x in stages)
 assert stages[1]['argv'][-2:]==['-v',m] and stages[1]['argv'][0].endswith('/leanchecker')
 signatures=[]
 for label in ['NORMAL','REPLAY','AUDIT']:
  for phase in ['BEFORE','AFTER']:
   c=json.loads(files[stage+label+'_'+phase+'_CONTEXT.json'])
   assert c['external_files']==15940 and c['external_map_sha256']==v['external_map_sha256']
   assert c['manifest_sha256']==v['source_manifest_sha256'] and c['source_sha256']==q['source_sha256']
   signatures.append(c['project_dependencies'])
   if (label,phase)!=('NORMAL','BEFORE'): assert c['owner_object_sha256']==q['sha256']
 assert all(x==signatures[0] for x in signatures)
 marks=collections.defaultdict(list)
 for line in files[stage+'AUDIT.log'].decode().splitlines():
  if line.startswith(('P0_QUEUE_','P25_PRIVATE_SCOPED_SIMP_INTERFACE ')):
   key,body=line.split(' ',1);marks[key].append(json.loads(body))
 inv,=marks['P0_QUEUE_INVENTORY'];imports,=marks['P0_QUEUE_IMPORTS'];decls=marks['P0_QUEUE_DECL']
 names={d['name'] for d in decls}
 assert inv['module']==m and len(names)==len(decls)==r['owned_count']==q['owned_count']
 assert names==set(inv['serialized'])==set(inv['environment']) and set(expected[m])<=names
 assert (not names)==(name=='P2Saving16Cell03ScalarDecode')
 assert len(imports)==len(set(imports))
 assert {x for x in imports if x.startswith('ImbalancedChen.')}==set(signatures[0])|{m}
 for d in decls:
  assert d['module']==m and not any(d[k] for k in ['unsafe','partial','axiom'])
  assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and '⋯' not in d['type']
 actual_audit=files['audits/'+name+'.lean'].decode()
 wanted=template.replace('P2Saving16Cell00TypedPayload',name)
 if name=='P2Saving16Cell03ScalarDecode': wanted=wanted.replace('names.size > 0','names.size == 0')
 if name.endswith('FieldSimp'):
  appendix=(repo/'docs/source-only/20261126-p2-5-cell00-field-split/PRIVATE_SCOPED_SIMP_AUDIT_APPENDIX.lean').read_text().replace('Cell00','Cell03')
  private=re.findall(r'^private theorem (\w+)',src.decode(),re.M)
  names_text=',\n    '.join(json.dumps('ImbalancedChen.P2Saving16Cell03FieldDecode.'+n) for n in private)
  appendix=re.sub(r'(let expected : Array String := #\[).*?(\]\n  let simpTheorems)',lambda z:z[1]+names_text+z[2],appendix,count=1,flags=re.S)
  wanted+='\n'+appendix
  simp,=marks['P25_PRIVATE_SCOPED_SIMP_INTERFACE'];assert simp['required_count']==simp['matched_count']==len(private)==576
 assert actual_audit==wanted
 decl_count+=len(decls);records.append({'module':m,'owned_count':len(decls),'object_sha256':q['sha256']})
assert decl_count==v['total_new_owned_declarations']==2957
transfer=read(root/'SIMPLEX05_MINIMAL_TRANSFER.json')
new={m:q for m,q in transfer['project_dependencies'].items() if q['kind']=='new_Cell03_accepted_object'}
assert len(new)==7
with tarfile.open(root/'SIMPLEX05_NEW_DEPS.tar.xz','r:xz') as tar:
 members=tar.getmembers();assert len(members)==7 and all(x.isfile() for x in members)
 for item in members:
  m='.'.join(Path(item.name).with_suffix('').parts[1:]);q=new[m]
  assert item.name==q['path'] and item.size==q['bytes']
  data=tar.extractfile(item).read();assert sha(data)==q['sha256']==index[m]['sha256']
report={'schema':'p25-cell03-root-checkpoint-review-v1','accepted_owner_count':45,'owned_records':decl_count,'stage_results_checked':135,'stage_contexts_checked':270,'raw_files_checked':625,'unchanged_source_commit':publication,'audit_templates_checked':45,'seven_dependency_objects_checked':7,'all_63_accepted':False,'P2_5_proved':False,'evidence_sha256':sha((cp/'ACTUAL_EVIDENCE_DICT64.json.xz').read_bytes()),'dependency_archive_sha256':sha((root/'SIMPLEX05_NEW_DEPS.tar.xz').read_bytes()),'owners':records}
out=root/'ROOT_CHECKPOINT_REVIEW.json';out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
print(json.dumps({k:x for k,x in report.items() if k!='owners'},indent=2))
