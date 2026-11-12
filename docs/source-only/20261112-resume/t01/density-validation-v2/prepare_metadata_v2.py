"""Pure source/metadata preparation; never executes the remote programs."""
from pathlib import Path
import hashlib,json,re
B=Path('E:/timot/Documents/FilesForGPT/Myath');H=B/'output/resume-20261112/t01/density-validation-v2';V1=H.with_name('density-validation-v1');R=B/'goldbach-proof-continuation'
P2=B/'output/resume-20261112/p2-repair-r2';PUB='51859a24c91580f885afd2a781dcb48b07177529'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def put(n,v):(H/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def desc(p):
    b=p.read_bytes();return {'path':p.relative_to(H).as_posix(),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b)}
m=read(V1/'DENSITY_MANIFEST.json');old={r['module']:r for r in m['files']}
reg=read(P2/'REPAIR_REGISTRY.json');delta=[]
for repair in reg['modules']:
    name=repair['module']
    if name not in old:
        assert name=='ImbalancedChen.P4AOriginalExecutableLog32';continue
    pre=old[name];post=repair['repaired'];b=(P2/post['path']).read_bytes()
    assert pre['sha256']==repair['original']['sha256']
    assert len(b)==post['bytes'] and sha(b)==post['sha256'] and blob(b)==post['git_blob']
    ims=re.findall(r'^import\s+([^\r\n]+)',b.decode('utf-8-sig'),re.M)
    assert ims==pre['imports'] and repair['imports_unchanged'] and repair['theorem_headers_unchanged']
    new={'module':name,'install_path':pre['install_path'],'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b),'imports':ims,
         'origin':{'kind':'git','commit':PUB,'path':'docs/source-only/20261112-resume/p2-repair-r2/'+post['path']},
         'selection':'PUBLISHED_INDEPENDENTLY_REVIEWED_P2_R2_PROOF_BODY_ONLY'}
    delta.append({'module':name,'before':pre,'after':new,'original_repair_registry_sha256':sha((P2/'REPAIR_REGISTRY.json').read_bytes())})
    old[name]=new
assert len(delta)==3
m['files']=[old[r['module']] for r in m['files']]
source_id=sha(json.dumps([[n,old[n]['sha256']] for n in sorted(old)],ensure_ascii=True,separators=(',',':')).encode())
m['targets'][0]['source_identity_sha256']=source_id
reverse={n:set() for n in old}
for n,r in old.items():
    for dep in r['imports']:
        if dep in reverse:reverse[dep].add(n)
invalid={r['module'] for r in delta};queue=list(invalid)
while queue:
    for n in reverse[queue.pop()]-invalid:invalid.add(n);queue.append(n)
m['r2_source_invalidation_modules']=sorted(invalid)
m['semantic_forbidden_old_object_modules']=sorted(set(m['semantic_forbidden_old_object_modules'])|invalid)
put('R2_SOURCE_DELTA.json',{'schema':'FineDensity-explicit-P2-R2-three-source-delta','publication':PUB,'files':delta,'unchanged_module_names_and_imports':True,
    'excluded_repair_module':'ImbalancedChen.P4AOriginalExecutableLog32','source_identity_before':read(V1/'DENSITY_MANIFEST.json')['targets'][0]['source_identity_sha256'],
    'source_identity_after':source_id,'source_changed_or_transitively_invalidated_modules':sorted(invalid),'accepted_objects':[]})
m['mathematical_modules']=m['project_modules']+sorted(r['module'] for r in m['native_sources'])
m['audit_wrapper_modules']=[Path(r['install_path']).stem for r in m['audit_sources']]
assert m['audit_wrapper_modules']==['CandidateAudit','DensityAudit','T01Audit']
m['fresh_kernel_modules']=m['mathematical_modules']+m['audit_wrapper_modules']
assert len(set(m['mathematical_modules']))==1851 and len(set(m['fresh_kernel_modules']))==1854
m['fresh_kernel_module_set_sha256']=sha(json.dumps(sorted(m['fresh_kernel_modules']),sort_keys=True,separators=(',',':')).encode())
m['schema']='fine-density-exact-validation-manifest-v2';m['bundle_path']=m['bundle_path'].replace('density-validation-v1','density-validation-v2')
m['floor_target']=read(R/'docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/EXACT_INSTALL_MANIFEST-v3.json')['targets'][0]
assert len(m['floor_target']['declarations'])==len(m['floor_target']['declaration_modules'])==9
guard_args=m['source_elaboration_resource_options']['moreLeanArgs']
m['wrapper_build_lean_args']=guard_args+['-DwarningAsError=true']
m['compiler_profiles']={
 'project':{'configuration':m['inherited_T01']['project_lakefile'],'moreLeanArgs':guard_args,'definition_options':{'maxRecDepth':'100000','maxHeartbeats':'4000000'}},
 'goldbach':{'configuration':desc(H/'reused/goldbach-lakefile.toml'),'moreLeanArgs':[], 'definition_options':{},'revision':m['native_rev'],'selected_library':'MathlibNt'},
 'wrapper':{'definition_options':{'maxRecDepth':'100000','maxHeartbeats':'4000000','warningAsError':'true'},'explicit_args':m['wrapper_build_lean_args']}}
targets=read(V1/'PRINT_TARGETS.json');targets['source_identity_sha256']=source_id
targets['kernel_gate']='Build and independently replay all1851 mathematical modules plus CandidateAudit, DensityAudit, T01Audit (1854 total). Keep exactly1851 mathematical modules in the full serialized/nonempty declaration census; print-only wrappers are not mathematical suppliers.'
targets['mathematical_serialized_modules']=m['mathematical_modules'];targets['fresh_kernel_modules']=m['fresh_kernel_modules']
put('PRINT_TARGETS.json',targets)
m['audit_sources']=[{**desc(H/r['install_path']),'install_path':r['install_path']} for r in m['audit_sources']]
m['audit_source']=next(r for r in m['audit_sources'] if r['install_path']=='DensityAudit.lean')
m['legacy_audit_source']=next(r for r in m['audit_sources'] if r['install_path']=='CandidateAudit.lean')
names=[r['path'] for r in m['support_files']]+['bind_compile_receipts.py','audit_floor.py','reused/goldbach-lakefile.toml']
m['support_files']=[desc(H/n) for n in dict.fromkeys(names)]
put('DENSITY_MANIFEST.json',m)
put('V2_BEFORE_AFTER.json',{'schema':'FineDensity-v1-v2-protocol-delta','v1_manifest_sha256':sha((V1/'DENSITY_MANIFEST.json').read_bytes()),
    'v2_manifest_sha256':sha((H/'DENSITY_MANIFEST.json').read_bytes()),'mathematical_modules_before_after':[1851,1851],'kernel_modules_before_after':[1851,1854],
    'source_selection_delta':'R2_SOURCE_DELTA.json','data357_and_restricted22_unchanged':m['data_inputs']==read(V1/'DENSITY_MANIFEST.json')['data_inputs'] and m['full_final_paths']==read(V1/'DENSITY_MANIFEST.json')['full_final_paths'],
    'native43_original_source_records_unchanged':m['native_sources']==read(V1/'DENSITY_MANIFEST.json')['native_sources'],
    'new_joins':['exact original9 name/owner and independent #print axioms','native source canonical path/SHA/bytes/original blob joined pre/post/command/setup','each selected direct non-core import has real hash-bound public olean','effective normalized flags exactly match project/native/wrapper profiles; duplicate -D rejects','three compiled wrapper facet/source/command bindings','four pre/post and raw-output hashes retained in final index'],
    'remote_programs_executed_locally':False,'v1_changed':False})
print(json.dumps({'manifest_sha256':sha((H/'DENSITY_MANIFEST.json').read_bytes()),'source_identity_sha256':source_id,'r2_changed_modules':3,'invalidated_modules':len(invalid),'kernel_modules':1854}))
