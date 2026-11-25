import pathlib,json,hashlib,shutil,uuid,tarfile,gzip,base64,datetime
P=pathlib.Path
root=P('/workspace/p29-coordinate-20261125')
gate=P('/workspace/p29-coordinate-verification-20261125')
expected={'VALIDATION_RESULTS.json':'5551e789e861eb51123cb4f7e95a11b32f947da928750669f5e69729ed5b8e4c','SOURCE_AND_OUTPUTS_AFTER.json':'c746aeeadde7c0e60bb80a199415a629d6ab986a6ec008d7f674d17547ef3a19','INVENTORY_NAME_SET_CHECK.json':'4d2b5b8c42bab11db5429a8a315a82a0c77353bcd550e698022593b702a20ec8','DECLARATION_TYPES_AXIOMS.json':'81f48cbf9c15186621b34cad60c78a7dbf04cb810c0ba2812ed83c1f945115ef'}
def sha(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def stamp(p):
 s=P(p).stat();return[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def save(p,obj):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(obj,f,indent=2);f.write('\n')
for name,h in expected.items():assert sha(gate/name)==h,('receipt drift',name)
v=json.loads((gate/'VALIDATION_RESULTS.json').read_text())
assert v['result']=='PASS_COORDINATE_CORE_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED'
assert v['owned_declarations']==6
assert v['old_source_rebuilds']==0
assert v['actual_native_import_modules']==[] and v['actual_old_project_import_modules']==[]
assert v['observed_axioms']==['Classical.choice','Quot.sound','propext']
outputs=json.loads((gate/'SOURCE_AND_OUTPUTS_AFTER.json').read_text())
for path,r in outputs.items():assert P(path).stat().st_size==r['bytes'] and sha(path)==r['sha256'],('own drift',path)
bindings=json.loads((gate/'ACTUAL_IMPORT_PART_BINDINGS.json').read_text())
assert sha(gate/'ACTUAL_IMPORT_PART_BINDINGS.json')==v['actual_import_bindings_sha256']
refreshed=[]
for r in bindings['parts']:
 p=P(r['identity']['path']); s=stamp(p)
 assert str(p.resolve())==r['identity']['resolved_path']
 if s!=r['stat_snapshot']:
  assert s[2]==r['identity']['bytes'] and sha(p)==r['identity']['sha256'],('input drift',str(p))
  refreshed.append({'path':str(p),'original_stat_snapshot':r['stat_snapshot'],'current_stat_snapshot':s,'sha256':r['identity']['sha256']})
 assert stamp(p)==s
out=P('/workspace/p29-coordinate-export-20261126-'+uuid.uuid4().hex[:8]);out.mkdir()
payload=out/'payload';payload.mkdir()
origin={}
def copy(src,rel):
 src=P(src);assert src.is_file() and not src.is_symlink(),str(src)
 dst=payload/rel;dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists()
 shutil.copyfile(src,dst);assert sha(src)==sha(dst);origin[rel]=str(src)
for p in sorted(gate.rglob('*')):
 if p.is_file():copy(p,'verification/'+str(p.relative_to(gate)))
for path in outputs:copy(path,'project/'+str(P(path).relative_to(root)))
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:copy(root/name,'project/'+name)
for path,h in v['original_tools_sha256'].items():
 assert sha(path)==h
 copy(path,'audited-tools/'+P(path).name)
save(payload/'FINAL_RELEASE_SEAL.json',{'schema':'p29_coordinate_export_seal_v1','exported_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'job_id':'job_0669bcefd1614c419277f509c399904c','result':v['result'],'modules':v['modules'],'owned_declarations':6,'exact_receipt_hashes':expected,'actual_import_parts_checked':len(bindings['parts']),'input_stat_refreshes':refreshed,'all_source_outputs_sha256_checked':True,'no_compile_or_replay':True,'all_standard_import_replay_claim':False})
files=[]
for p in sorted(payload.rglob('*')):
 if p.is_file():files.append({'path':str(p.relative_to(payload)),'bytes':p.stat().st_size,'sha256':sha(p),'origin':origin.get(str(p.relative_to(payload)))})
save(payload/'FILE_MANIFEST.json',{'schema':'p29_coordinate_archive_files_v1','files':files})
archive=out/'coordinate-qualified.tar.gz'
with archive.open('xb')as f:
 with gzip.GzipFile(fileobj=f,mode='wb',compresslevel=9,mtime=0,filename='')as z:
  with tarfile.open(fileobj=z,mode='w')as t:
   for p in sorted(payload.rglob('*')):
    if p.is_file():
     info=t.gettarinfo(str(p),arcname=str(p.relative_to(payload)))
     info.uid=info.gid=info.mtime=0;info.uname=info.gname=''
     with p.open('rb')as h:t.addfile(info,h)
with tarfile.open(archive,'r:gz')as t:
 members=t.getmembers();assert len(members)==len(files)+1
 for m in members:
  assert m.isfile() and not m.name.startswith('/') and '..'not in P(m.name).parts
  assert hashlib.sha256(t.extractfile(m).read()).hexdigest()==sha(payload/m.name)
transport={'schema':'p29_coordinate_archive_transport_v1','archive_path':str(archive),'archive_bytes':archive.stat().st_size,'archive_sha256':sha(archive),'file_manifest_sha256':sha(payload/'FILE_MANIFEST.json'),'seal_sha256':sha(payload/'FINAL_RELEASE_SEAL.json'),'tar_member_count':len(files)+1,'output_directory':str(out),'no_compile_or_replay':True}
save(out/'TRANSPORT_MANIFEST.json',transport)
print(json.dumps({'kind':'transport','manifest':transport}),flush=True)
for name in ['VALIDATION_RESULTS.json','SOURCE_AND_OUTPUTS_AFTER.json','INVENTORY_NAME_SET_CHECK.json','DECLARATION_TYPES_AXIOMS.json']:
 p=gate/name
 print(json.dumps({'kind':'exact_text','name':name,'bytes':p.stat().st_size,'sha256':sha(p),'text':p.read_text()}),flush=True)
for name in ['FILE_MANIFEST.json','FINAL_RELEASE_SEAL.json']:
 p=payload/name
 print(json.dumps({'kind':'exact_text','name':name,'bytes':p.stat().st_size,'sha256':sha(p),'text':p.read_text()}),flush=True)
encoded=base64.b64encode(archive.read_bytes()).decode()
assert len(encoded)<6000000
print('P29_COORDINATE_ARCHIVE_BASE64',flush=True)
print(encoded,flush=True)
