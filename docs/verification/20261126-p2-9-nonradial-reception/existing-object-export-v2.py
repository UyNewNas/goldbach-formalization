from pathlib import Path
import base64,hashlib,io,json,tarfile

root=Path('/workspace/p2-9-20261125')
module='ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport'
rel=Path(*module.split('.'))
registry=root/'.lake/p2-private/records.json'
expected_source='3d6f71b982a984e7fdd880b21ab496237ebeb656bed24990dedcfec96dff74bd'
expected_source_blob='2091608eaeec53f3f8b60224fb7b10048642805e'
expected_object='0285b3ed20b8b8d3b5a540dab4f2c6e60a8120a0c6eead3f081036ae8dbe5883'
expected_record='b9798231004d75befa227ecf4d8b4b9a5238a8cd25413d1c19bd2fc4d27ad97f'
expected_closure='a5261ca78e6cba51f8d88906419b3baf19bdc07612f165105fc575e3ab7d78e7'
expected_receipt='70335088765bca1a2f6475b998a9e587343901a6767ed6748bca7a20fa5e8f45'
sha=lambda b:hashlib.sha256(b).hexdigest()
encode=lambda x:(json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
regbytes=registry.read_bytes();records=json.loads(regbytes);record=records[module]
assert sha(encode(record))==expected_record
assert record['module']==module and record['exit_code']==0 and record['new_strict_compile']is True
assert record['source_sha256']==expected_source and record['object_sha256']==expected_object
assert record['closure_signature']==expected_closure
assert record['deps']=={'ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension':'c80ed8b590734eb936bafd1a50889d1f431a8617bf21d059d7f4f30c4d68138c'}
members={};origins={};observed={}
def watch(path,expected=None):
    path=Path(path);before=path.stat();b=path.read_bytes();after=path.stat()
    assert(before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_ino,after.st_size,after.st_mtime_ns)
    assert expected is None or sha(b)==expected,(str(path),sha(b),expected)
    value={'origin':str(path),'bytes':len(b),'sha256':sha(b),'inode':after.st_ino,'mtime_ns':after.st_mtime_ns}
    if str(path)in observed:assert observed[str(path)]==value
    observed[str(path)]=value
    return b,value
def take(name,path,expected=None):
    assert name not in members and not name.startswith('/')and '..'not in Path(name).parts
    b,value=watch(path,expected);members[name]=b;origins[name]=value
    return b

source=take('source/'+str(rel.with_suffix('.lean')),root/record['source'],expected_source)
assert hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()==expected_source_blob
take('objects/'+str(rel.with_suffix('.olean')),record['object'],expected_object)
assert Path(record['object'])==root/'.lake/p2-private/lib'/rel.with_suffix('.olean')
receipt_path=root/'.lake/p2-private/audit'/module/'latest.json'
receipt=json.loads(take('original-audit/latest.json',receipt_path,expected_receipt))
assert receipt['accepted']is True and receipt['module']==module
assert receipt['object_sha256']==expected_object and receipt['source_sha256']==expected_source
assert receipt['compile_closure_signature']==expected_closure
assert receipt['audit']['exit_code']==0 and receipt['replay']['exit_code']==0
assert receipt['audit']['declaration_count']==6
for name,digest in receipt['artifacts'].items():
    take('original-artifacts/'+name,root/name,digest)
for i,attempt in enumerate(record['attempts'],1):
    take('original-normal/attempt'+str(i)+'.log',root/attempt['log'])
assert record['attempts'][-1]['exit_code']==0 and record['attempts'][-1]['log']==record['log']
assert record['attempts'][-1]['command']==record['command']

# Bind only the relevant record subgraph and the actual files it names.
# Other sessions may append or update unrelated entries in the shared registry.
closure={};work=[module]
while work:
    name=work.pop()
    if name in closure:continue
    current=records[name];assert current['exit_code']==0
    closure[name]=current
    for dep,digest in current.get('deps',{}).items():
        assert records[dep]['object_sha256']==digest
        work.append(dep)
snapshot=receipt['input_snapshot']['project']
assert set(snapshot)==set(closure) and len(closure)==6
assert receipt['replay_binding']['project']==snapshot
for name,entry in snapshot.items():
    current=closure[name]
    assert entry['source_sha256']==current['source_sha256']and entry['object_sha256']==current['object_sha256']
    assert str(root/entry['source'])==str(root/current['source'])
    assert entry['object']==current['object']
    watch(root/entry['source'],entry['source_sha256'])
    watch(entry['object'],entry['object_sha256'])
    for dep,digest in current.get('deps',{}).items():
        assert snapshot[dep]['object_sha256']==digest
compiler=Path(record['command'][0]);watch(compiler,record['toolchain']['lean_binary_sha256'])
watch(compiler.parent/'leanchecker',receipt['input_snapshot']['leanchecker_sha256'])
declaration_names=[n for n in members if n.endswith('/declarations.json')]
assert len(declaration_names)==1
declarations=json.loads(members[declaration_names[0]])
assert isinstance(declarations,dict)
assert declarations['declaration_count']==6
assert isinstance(declarations['declarations'],list)and len(declarations['declarations'])==6
members['ORIGINAL_RECORD.json']=encode(record)
members['ORIGINAL_RELEVANT_RECORDS.json']=encode(closure)
members['EXPORTER.py']=SOURCE_TEXT.encode()

after_registry=registry.read_bytes();after_records=json.loads(after_registry)
for name,value in closure.items():assert after_records[name]==value,('relevant record changed',name)
for path,value in observed.items():
    p=Path(path);s=p.stat()
    assert(s.st_ino,s.st_size,s.st_mtime_ns)==(value['inode'],value['bytes'],value['mtime_ns']),('observed file changed',path)
    assert sha(p.read_bytes())==value['sha256'],('observed bytes changed',path)
binding={
    'schema':'p29_nonradial_existing_object_export_v1','module':module,
    'source_sha256':expected_source,'source_git_blob':expected_source_blob,'object_sha256':expected_object,
    'original_record_canonical_sha256':expected_record,'original_closure_signature':expected_closure,
    'original_receipt_sha256':expected_receipt,'original_owned_declaration_count':6,
    'registry_origin':str(registry),'registry_sha256_before_informational_only':sha(regbytes),
    'registry_sha256_after_informational_only':sha(after_registry),'whole_registry_equality_required':False,
    'relevant_record_modules':sorted(closure),'original_relevant_records_sha256':sha(members['ORIGINAL_RELEVANT_RECORDS.json']),
    'all_relevant_records_and_actual_dependency_files_unchanged':True,
    'all_original_normal_attempt_logs_preserved':True,'source_object_original_audit_and_full_types_preserved':True,
    'origin_files':origins,'observed_actual_files':observed,
    'source_recompilations':0,'kernel_replays':0,'new_manuscript_credit':0,
    'remote_source_or_object_writes':0,
    'scope':'Read-only export of the already accepted six-owned NonradialSupport object. No new proof credit, no recompile, no qualification of a new receiver, and no whole-standard-import proof claim.'}
members['BINDING_RECEIPT.json']=encode(binding)
manifest={'schema':'p29_nonradial_object_archive_manifest_v1','module':module,
    'files':{name:{'bytes':len(b),'sha256':sha(b)}for name,b in sorted(members.items())},
    'source_recompilations':0,'kernel_replays':0,'new_manuscript_credit':0}
members['FILE_MANIFEST.json']=encode(manifest)
buffer=io.BytesIO()
with tarfile.open(fileobj=buffer,mode='w:gz')as tf:
    for name,b in sorted(members.items()):
        item=tarfile.TarInfo(name);item.size=len(b);item.mtime=0;item.mode=0o644;tf.addfile(item,io.BytesIO(b))
archive=buffer.getvalue();assert len(archive)<1000000,'Archive too large for one bounded stdout export'
print(json.dumps({'archive_format':'tar.gz','archive_bytes':len(archive),'archive_sha256':sha(archive),
    'members':len(members),'file_manifest_sha256':sha(members['FILE_MANIFEST.json']),
    'binding_receipt_sha256':sha(members['BINDING_RECEIPT.json']),'object_sha256':expected_object,
    'original_owned_count':6,'no_lean_invocation':True,'new_manuscript_credit':0}),flush=True)
print('P29_NONRADIAL_ARCHIVE_BASE64',flush=True)
print(base64.b64encode(archive).decode(),flush=True)
