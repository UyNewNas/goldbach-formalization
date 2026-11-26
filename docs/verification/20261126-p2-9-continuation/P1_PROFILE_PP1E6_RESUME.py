import os,sys,pathlib,json,hashlib,subprocess,signal,time,datetime,re,importlib.util,traceback,tomllib,tarfile,ast
P=pathlib.Path
def sha(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()

def stamp(p):
 s=P(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

def save(p,x):
 p=P(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(x,f,indent=2);f.write('\n')

def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()

root=P('/workspace/p29-radial-profile-20261125-pinbind-v4')
out=P('/workspace/p29-radial-profile-verification-20261125-pinbind-v4')
assert root.is_dir()and out.is_dir()
original_driver=out/'driver.py'
assert sha(original_driver)=='ceb4f796dc7a362e47ae49fb0a2300f425c769500610e7c8baa09a6580b2170e'
assert not(out/'driver-pp1e6-resume.py').exists(),'Do not repeat a submitted continuation.'
original_tree=ast.parse(original_driver.read_text())
original_literals={n.targets[0].id:ast.literal_eval(n.value)for n in original_tree.body if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)and isinstance(n.value,ast.Constant)}
INPUTS=json.loads(original_literals['INPUT_TEXT'])
AUDIT_TEMPLATE=json.loads(original_literals['AUDIT_TEXT'])
SUPPLY=P('/workspace/p29-native-supply-20261125')
oldroot=P('/workspace/p29-radial-20261125')
oldout=P('/workspace/p29-radial-verification-20261125')
three=oldout/'attempt-3-postnormal'
two=oldout/'fibre-tuple-attempt-3'
receive=P('/workspace/p29-p2-object-supply-20261125')
GUARD=P('/workspace/goldbach-formalization/docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/ci_runtime_guard.py')
RUNNER=P('/workspace/blue-build-tools/run_guarded.py')
OWNED=P('/workspace/blue-build-tools/validate_member_roots_owned.py')
PIN='leanprover/lean4:v4.33.0-rc1'
tools_expected={str(GUARD):'837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877',str(RUNNER):'c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526',str(OWNED):'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'}
assert all(sha(p)==h for p,h in tools_expected.items())
binding=SUPPLY/'supply-bindings/BINDING_RECEIPT.json'
assert sha(binding)=='bb7654da1ea6b5803ba812c3fe13a8212160061a252b84a4c31029208c3a5596'
assert json.loads(binding.read_text())['status']=='PASS_CURRENT_P1_EXISTING_NATIVE_SUPPLY'
assert sha(three/'VALIDATION_RESULTS.json')=='cfd743edf49b26a995a4d86f22c1d74f3440326cfeb5004d4843f27f00d4daf2'
three_receipt=json.loads((three/'VALIDATION_RESULTS.json').read_text())
assert sha(two/'VALIDATION_RESULTS.json')=='a7949e9f91e330d7c08ab67ab6c8112f2cc004c01509389d47de545fc6f2f3c8'
assert sha(two/'SOURCE_AND_OUTPUTS_AFTER.json')=='e974cd33e375cd76bce315aa97ecee6ff435b6a515ea89c3ff897ba99d57067a'
assert sha(two/'ACTUAL_IMPORT_PART_BINDINGS.json')=='a5504938ee9fd2e7efe28cb8d80d67cb6e2264e5934be3825f1c5522acb4c393'
two_receipt=json.loads((two/'VALIDATION_RESULTS.json').read_text())
assert three_receipt['result']=='PASS_THREE_EXACT_SOURCE_MODULES_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED'
assert two_receipt['result']=='PASS_TWO_EXACT_SOURCE_MODULES_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED'
assert {x['module']:x['sha256']for x in two_receipt['inputs']}=={
'ImbalancedChen.P2MarkedPrimeProductFibreCore':'ca2a53a58e6f6c858c513dbead63ae469c193f2b0760c2e0dd529144f53563bf',
'ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount':'20d878534ba9e3fea689a605759e6a349ff3efa675ce54cf7a4e3ca265ac50c2'}
received=json.loads((receive/'RECEPTION_RECEIPT.json').read_text())
assert received['sha256']=='c524f898ff7222d3a1173429e7bf4150f9f71272ba1ae5aa40a7f1bd0e4c4083'
assert sha(receive/'p2-exact-twelve-objects.tar.gz')==received['sha256']
invpath=receive/'contents/inventory.json'
assert sha(invpath)=='aa6465a6ccd1596a695305576933c655b7b9a7514fed559f608976752e1d9477'
p2_inventory=json.loads(invpath.read_text())
assert len(p2_inventory['modules'])==12
for name,row in p2_inventory['members'].items():
 p=receive/'contents'/name;assert p.stat().st_size==row['bytes']and sha(p)==row['sha256'],('Received member drift',name)
for row in INPUTS:assert hashlib.sha256(row['source'].encode()).hexdigest()==row['sha256']
accepted_old_config=json.loads("{\"lake-manifest.json\":{\"bytes\":3176,\"sha256\":\"0c1ed2f4476d4b54d5376b98606e861fd7ecc822ddf3977831f48469c83fc54b\"},\"lakefile.toml\":{\"bytes\":2632,\"sha256\":\"86b052b20a913c4527345da687a427d677c8922486e705f9c4bdb4e273606fef\"},\"lean-toolchain\":{\"bytes\":29,\"sha256\":\"62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef\"}}")
for name,rec in accepted_old_config.items():
 assert (oldroot/name).stat().st_size==rec['bytes']and sha(oldroot/name)==rec['sha256'],('Accepted old workspace configuration drift',name)
assert sha(oldout/'CONFIGURATION_ADAPTATION.json')=='f0b3447bf787dd9914f5486e161221f7a669678eca444e6a6908375265b94621'
assert sha(oldout/'runtime-evidence/state.json')=='8af37ef442df0e4dc7fcebe1d937509b1d526e9ea0e1a99b648efd350a047e22'
accepted_policy=json.loads((oldout/'runtime-evidence/state.json').read_text())['policy']
mods=[x['module']for x in INPUTS]
oldmods=list(three_receipt['modules'])+list(two_receipt['modules'])
p2mods=sorted(p2_inventory['modules'])
assert len(oldmods)==len(set(oldmods))==5 and not set(oldmods)&set(p2mods)
borrowedmods=oldmods+p2mods
borrows_doc=json.loads((out/'BORROWED_OBJECTS.json').read_text())
borrows=borrows_doc['objects']
assert borrows_doc['module_count']==17 and set(borrows)==set(borrowedmods)
lib=root/'.lake/build/lib/lean'
allowed_sources=set()
for row in INPUTS:
 p=root/(row['module'].replace('.','/')+'.lean')
 assert p.read_bytes()==row['source'].encode()and sha(p)==row['sha256']
 assert hashlib.sha1(b'blob '+str(p.stat().st_size).encode()+b'\0'+p.read_bytes()).hexdigest()==row['blob']
 assert json.loads((out/'input-blobs'/(row['module']+'.json')).read_text())=={k:v for k,v in row.items()if k!='source'}
 allowed_sources.add(str(p.resolve()))
 rel=row['module'].replace('.','/')
 for q in [lib/(rel+s)for s in ['.olean','.ilean','.trace']]+[root/'.lake/build/ir'/(rel+s)for s in ['.c','.setup.json']]:
  assert not q.exists(),('A new target already has outputs; do not repeat normal',q)
for name in ['P2_CURRENT_P1_QUALIFICATION.json','normal-build-process.json','VALIDATION_RESULTS.json','borrowed-full-owned-pp1e6-process.json']:
 assert not(out/name).exists(),('A continuation stage already exists',name)
cache_before={}
protected_outputs={}
knownparts={}
def register_part(path,identity,snapshot,authority):
 path=str(path);p=P(path);st=stamp(p)
 if st!=snapshot:assert sha(p)==identity['sha256'],('Accepted import drift',path)
 cache_before[path]=st
 row={'identity':{'path':path,'bytes':identity['bytes'],'sha256':identity['sha256']},'stat_snapshot':st,'authority':authority}
 for key in [path,str(p.resolve())]:
  if key in knownparts:assert knownparts[key]['identity']['sha256']==identity['sha256'],('Accepted aliases disagree',key)
  knownparts[key]=row

for row in json.loads((SUPPLY/'supply-bindings/IMPORT_PART_BINDINGS.json').read_text())['parts']:
 register_part(row['identity']['path'],row['identity'],row['current_stat_snapshot'],'accepted_native_twelve_import_part')
for prior in [three,two]:
 for row in json.loads((prior/'ACTUAL_IMPORT_PART_BINDINGS.json').read_text())['parts']:
  register_part(row['identity']['path'],row['identity'],row['stat_snapshot'],'accepted_p1_five_import_part')
for prior in [SUPPLY,three,two]:
 doc=json.loads((prior/'SOURCE_AND_OUTPUTS_AFTER.json').read_text())
 for path,row in doc.items():
  assert P(path).stat().st_size==row['bytes']and sha(path)==row['sha256'],('Accepted source/output drift',path)
  protected_outputs[path]=row;cache_before[path]=stamp(path)
LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux').resolve()
TOOL_LIB=(TC/'lib/lean').resolve()
package_revisions={'mathlib': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1', 'plausible': 'b1c4a69a7e247ab7df20460212001673d74f08c0', 'LeanSearchClient': '0498c7c070c143a3bf7379f4d99a2c63bb9d9715', 'importGraph': '18a90119a5d316358fde6c86e0ca24e59212e32c', 'proofwidgets': 'b1436dc749e722c9920036b52cdc43b3451d0b69', 'aesop': '57d3325be72a842920813bcb40f96a6f7393c185', 'Qq': 'ee41917ae11d38479fb8fb24745f7ca4bf0a784d', 'batteries': '41bd267b3f6b7252f6676af46d4ffc6783b64de9', 'Cli': 'da07ca808b6718cb2aed14dba154e5a08b8f8ecf'}
package_bindings={}
release_binding={}
def stage(label,command,stdin=None,allow_sources=(),allow_audit=False,timeout=900):
 initial=guardlog.stat().st_size;pos=initial;pending=b'';rows=[];bad=[];started=utc();t0=time.monotonic();last=t0
 log=out/(label+'.log')
 with log.open('xb')as f:
  proc=subprocess.Popen(command,cwd=root,env=base_env,stdin=subprocess.PIPE if stdin is not None else None,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  if stdin is not None:proc.stdin.write(stdin);proc.stdin.close()
  while True:
   with guardlog.open('rb')as g:g.seek(pos);raw=g.read();pos+=len(raw)
   pending+=raw;lines=pending.split(b'\n');pending=lines.pop()
   for line in lines:
    if not line.strip():continue
    row=json.loads(line);rows.append(row)
    if row.get('tool')=='lean':
     args=row.get('input_args',[])
     if '--stdin'in args and not allow_audit:bad.append({'reason':'UNEXPECTED_STDIN_AUDIT','record':row})
     for a in args:
      if str(a).endswith('.lean'):
       q=P(a);q=q if q.is_absolute()else P(row['cwd'])/q
       if str(q.resolve())not in allow_sources and not(allow_audit and q.resolve().is_relative_to(out.resolve())):
        bad.append({'reason':'UNAUTHORIZED_SOURCE_REBUILD','record':row})
   code=proc.poll()
   if code is not None:break
   if bad or time.monotonic()-t0>timeout:
    os.killpg(proc.pid,signal.SIGTERM)
    try:proc.wait(timeout=10)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
    code=96 if bad else 124;break
   if time.monotonic()-last>=30:
    print(json.dumps({'stage':label,'root':str(root),'elapsed_seconds':round(time.monotonic()-t0,1),'forbidden_source_calls':len(bad)}),flush=True);last=time.monotonic()
   time.sleep(.2)
 if bad and code==0:code=96
 rec={'stage':label,'command':command,'cwd':str(root),'started_utc':started,'finished_utc':utc(),'exit_code':code,'guard_log_start':initial,'guard_log_end':pos,'guarded_commands':rows,'forbidden_source_calls':bad,'log_path':str(log),'log_sha256':sha(log)}
 if stdin is not None:rec['stdin_sha256']=hashlib.sha256(stdin).hexdigest()
 save(out/(label+'-process.json'),rec);runs.append(rec)
 print(json.dumps({'stage':label,'exit_code':code,'forbidden_source_calls':len(bad),'log_path':str(log)}),flush=True)
 if code:print(log.read_text()[-22000:],flush=True);raise RuntimeError('Gate failed: '+label)
 return rec

def facet_of(module,path):
 name=module.rsplit('.',1)[-1];base=P(path).name
 assert base.startswith(name+'.'),('Unexpected artifact name',module,path)
 return base[len(name):]

def bind_fresh_part(module,p):
 facet=facet_of(module,p)
 assert facet in {'.olean','.olean.server','.olean.private','.ir.sig','.ir'},('Unsupported import facet',module,p)
 expected=P(module.replace('.','/')+facet)
 if p.is_relative_to(TOOL_LIB):
  assert p.relative_to(TOOL_LIB)==expected,('Wrong pinned release member',module,p,expected)
  return 'fresh_actual_pinned_lean_release_part',{'provider':'leanprover/lean4','revision':LEAN_COMMIT,'provider_identity':'PINNED_TOOLCHAIN.json','relative_artifact':str(expected)}
 assert p.parts[-len(expected.parts):]==expected.parts,('Module-to-path mismatch',module,p)
 lib=p.parents[len(expected.parts)-1]
 assert lib.parts[-4:]==('.lake','build','lib','lean'),('Unbound package output root',module,p)
 pkg=lib.parents[3]
 # Only a package with the pinned manifest identity and an actual checkout
 # at its own top level can introduce a previously unbound external object.
 if str(pkg) not in package_bindings:
  def git(*args):
   return subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
  name=pkg.name
  assert name in package_revisions,('Unknown package',module,p,pkg)
  head=git('rev-parse','HEAD')
  assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and head==package_revisions[name],('Wrong pinned checkout',pkg,head)
  package_bindings[str(pkg)]={'name':name,'revision':head,'checkout':str(pkg),'lib_root':str(lib),'workspace_manifest_sha256':sha(root/'lake-manifest.json')}
 return 'fresh_actual_pinned_package_part',{**package_bindings[str(pkg)],'relative_artifact':str(expected)}

def compile_audit_text(module_names):
 names='#['+', '.join(chr(96)+m for m in module_names)+']'
 return AUDIT_TEMPLATE.replace('TARGET_MODULE_NAMES',names).encode()

def load_actual_imports(label,module_names,production=None):
 production=production or {}
 code=compile_audit_text(module_names)
 (out/(label+'.lean')).write_bytes(code)
 process=stage(label,runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin'],stdin=code,allow_audit=True)
 rows=[]
 for line in (out/(label+'.log')).read_text().splitlines():
  if line.startswith('P29_ACTUAL_IMPORT '):rows.append(json.loads(line[len('P29_ACTUAL_IMPORT '):]))
 assert rows and len(rows)==len({r['module']for r in rows})
 actual={r['module']:r for r in rows}
 assert set(module_names)<=set(actual)
 for module in actual:
  if module.startswith('ImbalancedChen.'):
   assert module in borrows or module in mods,('Unregistered project dependency',module)
 known_owned={str(P(row['object']).resolve()):(module,row)for module,row in borrows.items()}
 parts=[];counts={};hashes={}
 for row in rows:
  row['part_identities']=[]
  for pathrow in row['parts']:
   path=pathrow['resolved_path'];p=P(path);st=stamp(p);authority=None;original=None;provider_binding=None
   if path in known_owned:
    module,old=known_owned[path];assert module==row['module']
    assert st[2]==old['object_bytes']and sha(path)==old['object_sha256']
    identity={'path':path,'bytes':st[2],'sha256':old['object_sha256']}
    authority=old['origin'];original=old['original_object']
   elif path in production or str(p)in production:
    expected=production.get(path,production.get(str(p)));assert sha(p)==expected['sha256']
    identity={'path':path,**expected};authority='current_new_consumer_normal_output'
   elif path in knownparts or pathrow['path']in knownparts:
    old=knownparts.get(path,knownparts.get(pathrow['path']))
    op=old['identity']['path'];assert stamp(op)==cache_before[op],('Accepted input changed while audit ran',op)
    if st!=old['stat_snapshot']:assert sha(path)==old['identity']['sha256']
    identity={'path':path,'bytes':st[2],'sha256':old['identity']['sha256']};authority=old['authority'];original=op
   elif path in protected_outputs:
    expected=protected_outputs[path];assert sha(path)==expected['sha256']
    identity={'path':path,**expected};authority='accepted_native_owned_output'
   else:
    module=row['module']
    authority,provider_binding=bind_fresh_part(module,p)
    identity={'path':path,'bytes':st[2],'sha256':sha(path)}
   assert stamp(path)==st
   cache_before[path]=st
   record={'module':row['module'],'facet':facet_of(row['module'],path),'identity':identity,'requested_path':pathrow['path'],'stat_snapshot':st,'authority':authority}
   if provider_binding:record['provider_binding']=provider_binding
   if original:record['prior_bound_path']=original
   parts.append(record);row['part_identities'].append(record)
   counts[authority]=counts.get(authority,0)+1
   hashes[(row['module'],record['facet'])]=identity['sha256']
 data={'schema':'p29_current_actual_Lean_findOLean_import_graph_v1','roots':module_names,'module_count':len(rows),'part_count':len(parts),'counts':counts,'actual_modules':rows,'parts':parts,'loading_api':'Lean.importModules at private level; Lean.findOLean; default fallback facets as defined in pinned Lean.Environment.readModuleDataPartsOfMod/readIRPartsOfMod','constant_collision_check':'PASS importing all listed roots in one Environment'}
 save(out/(label+'-bindings.json'),data)
 return data,actual,hashes

def source_outputs():
 result={}
 for row in INPUTS:
  rel=row['module'].replace('.','/')
  paths=[root/(rel+'.lean')]+[root/'.lake/build/lib/lean'/(rel+s)for s in ['.olean','.ilean','.trace']]+[root/'.lake/build/ir'/(rel+s)for s in ['.c','.setup.json']]
  for p in paths:result[str(p)]={'bytes':p.stat().st_size,'sha256':sha(p)}
 return result

def named_kernel(label,module_names):
 rec=stage(label,runprefix+['lake','env','leanchecker','--verbose',*module_names])
 replayed=[l.removeprefix('replaying ')for l in (out/(label+'.log')).read_text().splitlines()if l.startswith('replaying ')]
 assert len(replayed)==len(set(replayed))==len(module_names)and set(replayed)==set(module_names)
 return rec

def full_owned(label,module_names):
 code=auditor.make_audit_code(module_names).encode();(out/(label+'.lean')).write_bytes(code)
 rec=stage(label,runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-Dpp.maxSteps=1000000','--stdin'],stdin=code,allow_audit=True)
 decls,inventory,axioms=auditor.read_audit((out/(label+'.log')).read_text(),module_names,rec['exit_code'])
 save(out/(label+'-DECLARATION_TYPES_AXIOMS.json'),decls)
 save(out/(label+'-INVENTORY_NAME_SET_CHECK.json'),inventory)
 return rec,decls,inventory,axioms

IMMUTABLE_PINS={'/workspace/p29-radial-profile-verification-20261125-pinbind-v4/FAILURE.json': 'ec27af46c62c1b54f95d1da40fc797944ebeb64b2972ad8aae692bcf5870e22e', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/P1_FIVE_IMPORT_COMPARISON.json': 'c28904e9a8c3dd671128810c1dd513bdd61ae6197944691b573652db6a65fbb1', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/CONFIGURATION_ADAPTATION.json': 'dc194749cdd6326b75cef7b5fb23aab94ac124c97e198df6f967a21bd76f04ac', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/PINNED_TOOLCHAIN.json': '0db147120993bccc43f38ac8b56dd6369ac1a1884b69b96146478a5edb89948a', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/BORROWED_OBJECTS.json': '01f254264580b22f22c2e20caaba30b13d309656099d7127f49e2d6cb5022562', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/borrowed-actual-imports-bindings.json': '68a4337c78570148b059c8abe0d0da9c360c3c7254b161ecab13d32f420d9e23', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/borrowed-full-owned.lean': '130d8d0b25fbad4ba5d0a1e24f1b5ffb0dc5928574f8ac19205be19683ec6081', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-setup-process.json': '9c302502f7c2940990ddbd52f178c91bce3f1f2677ab8e2f09fb8c77909a0025', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-initial-audit-process.json': '1294b9ab37253ee9cde3fd4ccef599f93fd3802597ead118d375876e0b6d59fa', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/pinned-lean-version-process.json': '26342beb362154da815a6edca4a09e63b1821178b61f5ec9a74cd69f38ba0a33', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/pinned-lean-prefix-process.json': '9d9f8a6d7c81d11b9db2960271ea4a01379676b26cf9c5b06ee7c3ce15e8ca5f', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/borrowed-actual-imports-process.json': '9011736e038a6f29c654737e75c86145df1f2bdb1f16f33bb4fa052b63aac0cf', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/borrowed-named-kernel-process.json': '85fe317f897a263d03d371f44d9d2ca332619d4039ef0639c9a9a25967fbff02', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/borrowed-full-owned-process.json': '2e33da3870fc99e20fc950de53da489b4444abf57b2789565d26deb29175a3cf', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/driver.py': 'ceb4f796dc7a362e47ae49fb0a2300f425c769500610e7c8baa09a6580b2170e', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/borrowed-full-owned.log': 'c5089f2c63489ab55c0a6cb01e76a75a5e9b23bc371c0beca05d303195d88d6e', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-evidence/state.json': '93dd7569b9434e6c5bc4a795fb194f7050dc8f9eee8eaf8fea15df56b3fe0bec'}
for p,h in IMMUTABLE_PINS.items():assert sha(p)==h,('Original immutable evidence changed',p)
state_path=out/'runtime-evidence/state.json';state=json.loads(state_path.read_text())
state_sha_before=sha(state_path);guardlog=P(state['log'])
assert state_sha_before=='93dd7569b9434e6c5bc4a795fb194f7050dc8f9eee8eaf8fea15df56b3fe0bec'
assert state['policy']==accepted_policy
for key in ['runtime_sha256','input_sha256','action_script_sha256']:
 for p,h in state[key].items():assert sha(p)==h,('Original runtime/input changed',p)
config_before={str(root/name):sha(root/name)for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
assert config_before==state['input_sha256']
original_guard_prefix=guardlog.read_bytes()
assert len(original_guard_prefix)==5232 and hashlib.sha256(original_guard_prefix).hexdigest()=='399761ebf8a3f51008311aaaedf3992863bef89eebba4694e89d2c28617d3e29'
old_commands=[json.loads(l)for l in original_guard_prefix.decode().splitlines()if l]
assert not any(r.get('tool')=='lean'and any(str(a).endswith('.lean')for a in r.get('input_args',[]))for r in old_commands)
initial_runtime_path=out/'runtime-evidence/audit.json'
initial_runtime_bytes=initial_runtime_path.read_bytes();initial_runtime=json.loads(initial_runtime_bytes)
assert initial_runtime['state_sha256']==state_sha_before and initial_runtime['status']=='PASS_RUNTIME_GUARD_ONLY'
runtime_parent=root/'runtime'
base_env=os.environ.copy()
for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR='/workspace/blue-build-tools/lean-action',GITHUB_ENV=str(out/'runtime.env'),GITHUB_PATH=str(out/'runtime.path'))
base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
runprefix=['python3',str(RUNNER),'--state',str(state_path)]
runs=[]
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED)
auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
before=json.loads((out/'borrowed-actual-imports-bindings.json').read_text())
assert before['roots']==borrowedmods and before['module_count']==6197 and before['part_count']==30833
actual={r['module']:r for r in before['actual_modules']}
hashes={}
for part in before['parts']:
 path=part['identity']['path'];ident=part['identity'];p=P(path)
 assert stamp(p)==part['stat_snapshot']and p.stat().st_size==ident['bytes']and sha(p)==ident['sha256'],('Previously bound actual part changed',path)
 register_part(path,ident,part['stat_snapshot'],part['authority'])
 if part['requested_path']in knownparts:assert knownparts[part['requested_path']]['identity']['sha256']==ident['sha256']
 else:knownparts[part['requested_path']]=knownparts[path]
 key=(part['module'],part['facet']);assert key not in hashes;hashes[key]=ident['sha256']
 provider=part.get('provider_binding',{})
 if 'checkout'in provider and provider['checkout']not in package_bindings:
  pkg=P(provider['checkout']);name=provider['name']
  assert name in package_revisions and provider['revision']==package_revisions[name]
  git=lambda *args:subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
  assert P(git('rev-parse','--show-toplevel')).resolve()==pkg.resolve()and git('rev-parse','HEAD')==provider['revision']
  package_bindings[str(pkg)]={k:provider[k]for k in ['name','revision','checkout','lib_root','workspace_manifest_sha256']}
for module,row in borrows.items():
 assert sha(row['source'])==row['source_sha256']and sha(row['object'])==row['object_sha256']
 assert P(row['object']).stat().st_size==row['object_bytes']and P(row['object'])==lib/(module.replace('.','/')+'.olean')
 cache_before[str(P(row['source']))]=stamp(row['source'])
 if module in p2mods:
  original=p2_inventory['modules'][module]['record']
  assert row['original_compile_record']==original and row['source_sha256']==original['source_sha256']and row['object_sha256']==original['object_sha256']
  assert sha(row['received_object'])==row['object_sha256'];cache_before[row['received_object']]=stamp(row['received_object'])
 else:
  assert row['object_sha256']==protected_outputs[row['original_object']]['sha256']
comparison=json.loads((out/'P1_FIVE_IMPORT_COMPARISON.json').read_text())
assert comparison['affected_modules']==[]and comparison['drift']==[]and comparison['all_original_facet_bytes_preserved']is True
assert [r['module']for r in comparison['modules']]==oldmods
for row in comparison['modules']:assert sha(row['original_setup_path'])==row['original_setup_sha256']
affected=comparison['affected_modules']
for module in p2mods:
 rec=p2_inventory['modules'][module]['record']
 for dep,h in rec.get('deps',{}).items():assert hashes.get((dep,'.olean'))==h
 projimports=[x for x in actual[module]['direct_imports']if x.startswith('ImbalancedChen.')]
 assert set(projimports)==set(rec.get('deps',{}))
supply_mods=p2mods+affected
release_binding=json.loads((out/'PINNED_TOOLCHAIN.json').read_text())
assert release_binding['pin']==PIN and release_binding['lean_commit']==LEAN_COMMIT
assert release_binding['guarded_shadow']['state_sha256']==state_sha_before
shadow=P(state['shadow'])
assert P(state['realbin'])==(TC/'bin').resolve()and(shadow/'lib').is_symlink()and(shadow/'lib/lean').resolve()==TOOL_LIB
assert release_binding['guarded_shadow']['prefix']==str(shadow)
for name,shadow_name in [('lean','lean-runtime'),('lake','lake')]:
 p=TC/'bin'/name;q=shadow/'bin'/shadow_name
 assert p.is_file()and q.is_file()and not q.is_symlink()
 assert sha(p)==sha(q)==release_binding[name]['sha256']==state['runtime_sha256'][str(p)]==state['runtime_sha256'][str(q)]
 cache_before[str(p)]=stamp(p);cache_before[str(q)]=stamp(q)
old_stage_labels=['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','borrowed-actual-imports','borrowed-named-kernel','borrowed-full-owned']
old_stages={}
for label in old_stage_labels:
 rec=json.loads((out/(label+'-process.json')).read_text())
 assert rec['exit_code']==0 and rec['cwd']==str(root)and not rec['forbidden_source_calls']and sha(rec['log_path'])==rec['log_sha256']
 old_stages[label]=rec
assert old_stages['pinned-lean-version']['command']==runprefix+['lake','env','lean','--version']
assert old_stages['pinned-lean-prefix']['command']==runprefix+['lake','env','lean','--print-prefix']
assert old_stages['borrowed-actual-imports']['command']==runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin']
assert (out/'borrowed-actual-imports.lean').read_bytes()==compile_audit_text(borrowedmods)
assert old_stages['borrowed-actual-imports']['stdin_sha256']==sha(out/'borrowed-actual-imports.lean')
supply_kernel=old_stages['borrowed-named-kernel']
assert supply_kernel['command']==runprefix+['lake','env','leanchecker','--verbose',*supply_mods]
replayed=[l.removeprefix('replaying ')for l in (out/'borrowed-named-kernel.log').read_text().splitlines()if l.startswith('replaying ')]
assert len(replayed)==len(set(replayed))==len(supply_mods)==12 and set(replayed)==set(supply_mods)
original_audit=auditor.make_audit_code(supply_mods).encode()
assert (out/'borrowed-full-owned.lean').read_bytes()==original_audit
assert old_stages['borrowed-full-owned']['command']==runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin']
assert old_stages['borrowed-full-owned']['stdin_sha256']==hashlib.sha256(original_audit).hexdigest()
old_raw=(out/'borrowed-full-owned.log').read_text()
old_rows=[json.loads(l.removeprefix('MEMBER_OWNED_DECL '))for l in old_raw.splitlines()if l.startswith('MEMBER_OWNED_DECL ')]
old_issues=[{'name':r['name'],'module':r['module'],'field':key,'characters':len(r[key]),'ellipsis_count':r[key].count('⋯')+r[key].count('...')}for r in old_rows for key in ['type','type_expression']if '⋯'in r[key]or '...'in r[key]]
assert len(old_rows)==327 and len({r['name']for r in old_rows})==327
assert old_issues==[{'name':'ImbalancedChen.P2FiniteMarkedGamma5LogExtension.marginRow.eq_7','module':'ImbalancedChen.P2FiniteMarkedGamma5DerivativeBudget','field':'type','characters':73447,'ellipsis_count':14}]
assert hashlib.sha256(next(r['type']for r in old_rows if r['name']==old_issues[0]['name']).encode()).hexdigest()=='02f70feaeedb5f7dc0b4c354c553b8939fd399b0a4deb094b90837e3902c6a0b'
options_source=TC/'src/lean/Lean/PrettyPrinter/Delaborator/Options.lean'
assert sha(options_source)=='d0a49b7a18cc5d9efa691c86be8bd64cccef4ec982cfbebb6c412813819f3f50'
assert 'register_builtin_option pp.maxSteps : Nat := {\n  defValue := 5000'in options_source.read_text()
for p,h in IMMUTABLE_PINS.items():assert sha(p)==h
assert all(sha(p)==h for p,h in tools_expected.items())
assert all(P(p).is_file()and stamp(p)==s for p,s in cache_before.items())
with(out/'driver-pp1e6-resume.py').open('x')as f:f.write(SOURCE_TEXT)
with(out/'INITIAL_RUNTIME_REPORT_PRESERVED.json').open('xb')as f:f.write(initial_runtime_bytes)
with(out/'ORIGINAL_GUARD_LOG_PREFIX.jsonl').open('xb')as f:f.write(original_guard_prefix)
with(out/'PINNED_LEAN_PRETTY_PRINTER_OPTIONS.lean').open('xb')as f:f.write(options_source.read_bytes())
save(out/'PP_MAX_STEPS_RESUME_CONTEXT.json',{'schema':'p29_profile_pp_max_steps_exact_resume_v1','original_driver_sha256':sha(original_driver),'original_failure_sha256':sha(out/'FAILURE.json'),'original_log_sha256':sha(out/'borrowed-full-owned.log'),'read_only_diagnostic_blob':'6a2470ced72577476489e61838344f1dfa2a57dc','original_issue':old_issues,'reason':'The sole 14-ellipsis pretty type is byte-identical to the prior UnitTail pp.maxSteps=5000 case. All 327 original raw ASTs are complete. Only the incomplete display stage is repeated with pp.maxSteps=1000000.','same_audit_source_sha256':hashlib.sha256(original_audit).hexdigest(),'original_tools':tools_expected,'reused_stages':old_stages,'actual_import_bindings_sha256':sha(out/'borrowed-actual-imports-bindings.json'),'actual_parts_verified_unchanged':len(before['parts']),'original_guard_prefix_sha256':hashlib.sha256(original_guard_prefix).hexdigest(),'preserved_initial_runtime_report_sha256':sha(out/'INITIAL_RUNTIME_REPORT_PRESERVED.json'),'source_compilations_before_resume':0,'no_repeated_kernel_or_actual_import_probes':True,'extra_proof_credit':0})
try:
 supply_owned,supply_decls,supply_inventory,supply_axioms=full_owned('borrowed-full-owned-pp1e6',supply_mods)
 old_by_name={r['name']:r for r in old_rows};new_by_name={r['name']:r for r in supply_decls}
 assert set(old_by_name)==set(new_by_name)and len(new_by_name)==327
 for name,old in old_by_name.items():
  new=new_by_name[name]
  assert {k:v for k,v in old.items()if k!='type'}=={k:v for k,v in new.items()if k!='type'},('Raw AST/owner/kind/universe/axiom changed',name)
  if name!=old_issues[0]['name']:assert old['type']==new['type'],('Previously complete pretty type changed',name)
 save(out/'PP_MAX_STEPS_RESOLUTION.json',{'schema':'p29_profile_pp_max_steps_complete_output_v1','prior_issues':old_issues,'all_327_original_raw_AST_owner_kind_universe_axiom_records_identical':True,'other_326_pretty_types_identical':True,'eliminated_pretty_ellipsis_count':14,'new_ellipsis_count':0,'reprinted_stage':supply_owned,'original_validator_unchanged':sha(OWNED),'new_proof_credit_for_reprint':0})
 for p,h in IMMUTABLE_PINS.items():assert sha(p)==h
 assert all(P(p).is_file()and stamp(p)==s for p,s in cache_before.items())
 for module,row in borrows.items():assert sha(row['object'])==row['object_sha256']
 supply_receipt={'schema':'p29_P2_exact_objects_current_P1_carrier_qualification_v1','result':'PASS_CURRENT_P1_RESOLVED_INPUTS_NAMED_KERNEL_FULL_OWNED_ZERO_SOURCE_REBUILD','original_P2_export_job':'e90d8d7e7720478ead08403a1d45d2d6','original_packet_blob':'45cb5e4272907279bd0fe0d13c3169995ab3889b','original_packet_sha256':received['sha256'],'original_inventory_sha256':sha(invpath),'original_producer_facets':['.olean'],'original_standard_Mathlib_part_hashes_not_recorded':True,'old_and_current_standard_Mathlib_byte_equality_claim':False,'borrowed_objects':borrows,'P2_modules_requalified':p2mods,'P1_old_modules_with_changed_actual_inputs_requalified':affected,'current_input_bindings_sha256':sha(out/'borrowed-actual-imports-bindings.json'),'original_P1_comparison_sha256':sha(out/'P1_FIVE_IMPORT_COMPARISON.json'),'kernel':supply_kernel,'owned':supply_owned,'owned_declarations':len(supply_decls),'owned_declaration_counts':supply_inventory['module_counts'],'observed_axioms':supply_axioms,'all_owned_private_generated_types_universes':True,'source_compilations':0,'new_mathematical_theorem_credit':0,'scope_note':'Original exact proof objects are requalified under the explicitly bound current P1 carrier. This does not invent absent old producer trace/setup, or claim byte equality of unrecorded original standard Mathlib parts.'}
 supply_receipt.update(pp_max_steps_resume_context_sha256=sha(out/'PP_MAX_STEPS_RESUME_CONTEXT.json'),pp_max_steps_resolution_sha256=sha(out/'PP_MAX_STEPS_RESOLUTION.json'),original_327_AST_unchanged_after_complete_printing=True,reused_original_kernel_without_replay=True,reused_actual_inputs_with_complete_hash_stability_check=True)
 save(out/'P2_CURRENT_P1_QUALIFICATION.json',supply_receipt)
 print(json.dumps({'stage':'P2-current-P1-supply-qualified','modules':len(p2mods),'additional_P1_affected_modules':affected,'owned':len(supply_decls),'receipt':str(out/'P2_CURRENT_P1_QUALIFICATION.json'),'receipt_sha256':sha(out/'P2_CURRENT_P1_QUALIFICATION.json'),'source_recompilations':0}),flush=True)
 normal=stage('normal-build',runprefix+['lake','build',*['+'+m+':olean'for m in mods]],allow_sources=allowed_sources)
 production=source_outputs();save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',production)
 after,actual_after,hashes_after=load_actual_imports('consumer-actual-imports',mods,production)
 setup_matches=[]
 for module in mods:
  path=root/'.lake/build/ir'/(module.replace('.','/')+'.setup.json')
  setup=json.loads(path.read_text());assert setup['name']==module
  checked=0
  for dep,groups in setup['importArts'].items():
   for group in groups:
    for p in group:
     assert hashes_after.get((dep,facet_of(dep,p)))==sha(p),('Lake actual importArts override differs from probed loader carrier',module,dep,p)
     checked+=1
  setup_matches.append({'module':module,'setup_path':str(path),'setup_sha256':sha(path),'explicit_setup_artifact_count':checked,'explicit_parts_match_current_resolver':True,'unlisted_external_imports_bound_via_actual_loader_graph':True})
 save(out/'CONSUMER_SETUP_IMPORT_MATCH.json',setup_matches)
 kernel=named_kernel('named-kernel',mods)
 owned,decls,inventory,axioms=full_owned('full-owned',mods)
 stock=stage('final-stock',runprefix+['lake','--no-build','build',*['+'+m+':olean'for m in mods]])
 assert not any(r.get('tool')=='lean'and('--stdin'in r.get('input_args',[])or any(str(a).endswith('.lean')for a in r.get('input_args',[])))for r in stock['guarded_commands'])
 stage('runtime-final-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe','--require-source'])
 final=source_outputs();assert final==production
 assert sha(state_path)==state_sha_before
 assert {p:sha(p)for p in config_before}==config_before
 assert all(sha(oldroot/name)==rec['sha256']for name,rec in accepted_old_config.items())
 assert all(sha(p)==h for p,h in tools_expected.items())
 assert all(sha(p)==r['sha256']for p,r in protected_outputs.items())
 changed=[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s]
 assert not changed,('Accepted or received cache changed',changed[:20])
 for m,r in borrows.items():assert sha(r['object'])==r['object_sha256']
 save(out/'SOURCE_AND_OUTPUTS_AFTER.json',final)
 for p,h in IMMUTABLE_PINS.items():assert sha(p)==h
 assert guardlog.read_bytes().startswith(original_guard_prefix)
 all_commands=[json.loads(l)for l in guardlog.read_text().splitlines()if l]
 source_calls=[str((P(r['cwd'])/a).resolve())if not P(a).is_absolute()else str(P(a).resolve())for r in all_commands if r.get('tool')=='lean'for a in r.get('input_args',[])if str(a).endswith('.lean')]
 assert len(source_calls)==2 and set(source_calls)==allowed_sources,source_calls
 result={'schema':'p29_profile_natural_normal_stock_named_kernel_full_owned_v1','result':'PASS_TWO_NEW_CONSUMERS_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED','root':str(root),'evidence':str(out),'modules':mods,'inputs':[{k:v for k,v in row.items()if k!='source'}for row in INPUTS],'normal':normal,'kernel':kernel,'owned':owned,'stock':stock,'owned_declarations':len(decls),'owned_declaration_counts':inventory['module_counts'],'observed_axioms':axioms,'full_owned_private_generated_ast_universes':True,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'runtime_policy':state['policy'],'original_audited_tools_unchanged':tools_expected,'native_twelve_receipt_sha256':sha(binding),'original_three_receipt_sha256':sha(three/'VALIDATION_RESULTS.json'),'original_fibre_tuple_receipt_sha256':sha(two/'VALIDATION_RESULTS.json'),'P2_current_P1_supply_qualification_sha256':sha(out/'P2_CURRENT_P1_QUALIFICATION.json'),'actual_import_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'consumer_setup_import_match_sha256':sha(out/'CONSUMER_SETUP_IMPORT_MATCH.json'),'recompiled_old_project_or_native_sources':0,'all_import_replay_claim':False,'scope_note':'These are the original single fixed-split ambient profile outer mass and the exact natural tuple sum dictionary. No whole-history aggregation, original J identification, additive-prime test, or moving-family PP estimate is claimed.'}
 result.update(pp_max_steps_resolution_sha256=sha(out/'PP_MAX_STEPS_RESOLUTION.json'),resume_context_sha256=sha(out/'PP_MAX_STEPS_RESUME_CONTEXT.json'),normal_source_invocations=source_calls,borrowed_kernel_replayed_in_resume=False,borrowed_actual_import_probe_repeated=False,original_failed_full_owned_log_retained=True)
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','root','evidence','modules','owned_declarations','owned_declaration_counts','observed_axioms','monitored_parts_unchanged','actual_import_bindings_sha256']}),flush=True)
 print(json.dumps({'validation_results_sha256':sha(out/'VALIDATION_RESULTS.json'),'source_outputs_sha256':sha(out/'SOURCE_AND_OUTPUTS_AFTER.json'),'declarations_sha256':sha(out/'full-owned-DECLARATION_TYPES_AXIOMS.json'),'inventory_sha256':sha(out/'full-owned-INVENTORY_NAME_SET_CHECK.json')}),flush=True)
except Exception as e:
 failure={'schema':'p29_profile_natural_pp1e6_resume_failure_v1','root':str(root),'evidence':str(out),'error':str(e),'traceback':traceback.format_exc(),'completed_resume_stages':[r['stage']for r in runs],'reused_original_stages':old_stage_labels,'original_failure_sha256':sha(out/'FAILURE.json'),'borrowed_cache_changed':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s]}
 save(out/'FAILURE_pp1e6_resume.json',failure)
 print(json.dumps(failure),flush=True)
 raise
if 'result' in globals() and result.get('result')=='PASS_TWO_NEW_CONSUMERS_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED':
 import base64
 export=out/'portable';export.mkdir()
 take=[out/'VALIDATION_RESULTS.json',out/'SOURCE_AND_OUTPUTS_AFTER.json',out/'full-owned-DECLARATION_TYPES_AXIOMS.json',out/'full-owned-INVENTORY_NAME_SET_CHECK.json',out/'borrowed-full-owned-pp1e6-DECLARATION_TYPES_AXIOMS.json',out/'borrowed-full-owned-pp1e6-INVENTORY_NAME_SET_CHECK.json',out/'P2_CURRENT_P1_QUALIFICATION.json',out/'P1_FIVE_IMPORT_COMPARISON.json',out/'CONSUMER_SETUP_IMPORT_MATCH.json',out/'CONFIGURATION_ADAPTATION.json',out/'PINNED_TOOLCHAIN.json',out/'BORROWED_OBJECTS.json']
 take+=[out/name for name in ['PP_MAX_STEPS_RESOLUTION.json','PP_MAX_STEPS_RESUME_CONTEXT.json','FAILURE.json','INITIAL_RUNTIME_REPORT_PRESERVED.json','ORIGINAL_GUARD_LOG_PREFIX.jsonl','driver.py','driver-pp1e6-resume.py']]
 take+=sorted(out.glob('*-process.json'))+[out/'runtime-evidence/state.json',guardlog]
 entries={'config/'+name:root/name for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
 for path in final:
  p=P(path);entries['project/'+str(p.relative_to(root))]=p
 for p in take:
  name=str(p.relative_to(out))if p.is_relative_to(out)else 'runtime-evidence/actual-guard-log.jsonl'
  entries['evidence/'+name]=p
 portable=export/'PROFILE_NATURAL_REUSABLE_OBJECTS_AND_ORIGINAL_AUDITS.tar.xz'
 def pack(destination,members):
  with tarfile.open(destination,'w:xz',preset=3)as tar:
   for k,v in sorted(members.items()):tar.add(v,arcname=k,recursive=False)
 member_inventory={name:{'bytes':p.stat().st_size,'sha256':sha(p)}for name,p in entries.items()}
 save(export/'MEMBERS.json',member_inventory);entries['MEMBERS.json']=export/'MEMBERS.json'
 pack(portable,entries)
 complete=export/'PROFILE_NATURAL_COMPLETE_EVIDENCE.tar.xz'
 complete_entries={'evidence/'+str(p.relative_to(out)):p for p in out.rglob('*')if p.is_file()and export not in p.parents}
 complete_entries.update({k:v for k,v in entries.items()if k.startswith(('project/','config/'))})
 complete_inventory={name:{'bytes':p.stat().st_size,'sha256':sha(p)}for name,p in complete_entries.items()}
 save(export/'COMPLETE_MEMBERS.json',complete_inventory);complete_entries['COMPLETE_MEMBERS.json']=export/'COMPLETE_MEMBERS.json'
 pack(complete,complete_entries)
 sent=0
 for p in [portable,complete]:
  emit=(sent+p.stat().st_size)<=5600000
  print('P29_ARCHIVE '+json.dumps({'name':p.name,'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p),'emitted':emit,'files':len(entries)if p==portable else len(complete_entries)}),flush=True)
  if emit:
   print('P29_DATA '+p.name+' '+base64.b64encode(p.read_bytes()).decode(),flush=True);sent+=p.stat().st_size
