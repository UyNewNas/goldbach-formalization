import pathlib,os,sys,json,hashlib,subprocess,time,signal,datetime,traceback,shutil,tomllib,importlib.util,urllib.request,base64,re,tarfile
P=pathlib.Path
sys.dont_write_bytecode=True
base=P('/workspace/p29-gate-affine-20261126-ba9b1989')
oldbase=P('/workspace/p29-unit-tail-20261126-8131f7d6')
oldout=oldbase/'verification'
root=base/'project';out=base/'verification'
assert not base.exists(),'Do not repeat this independent Gate receiver; read its existing receipt first.'
base.mkdir();root.mkdir();out.mkdir()
(out/'driver.py').write_text(SOURCE_TEXT)
def sha(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def stamp(p):
 s=P(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def save(p,x):
 p=P(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(x,f,indent=2);f.write('\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def get_blob(blob):
 d=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=45))
 assert d['encoding']=='base64'
 b=base64.b64decode(d['content'])
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
 return b
target='ImbalancedChen.P2FiniteMarkedGamma5GateAffine'
source_blob='fddfeda6a91675472e8fb05dd8301f379bd1d111'
source_sha='ba9b1989c42a681de23ad448749c0f8a1a10ae77160dabc512f664b65cfa2b55'
source=get_blob(source_blob)
assert len(source)==10279 and hashlib.sha256(source).hexdigest()==source_sha
source_imports=re.findall(r'^import\s+(\S+)',source.decode(),re.M)
assert source_imports==['ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension','ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget','Mathlib.Algebra.BigOperators.Fin']
src=root/(target.replace('.','/')+'.lean');src.parent.mkdir(parents=True);src.write_bytes(source)
lib=root/'.lake/build/lib/lean';lib.mkdir(parents=True)
protected={};cache_before={};runs=[]
def preserve(p,expected=None):
 p=P(p);s=stamp(p);d=sha(p)
 assert stamp(p)==s
 if expected is not None:assert d==expected,(str(p),'hash mismatch')
 row={'bytes':s[2],'sha256':d};protected[str(p)]=row;cache_before[str(p)]=s
 return row
old_receipts={
 'SUPPLY_QUALIFICATION.json':'1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21',
 'BORROWED_OBJECTS.json':'3e7c6baf5d8ef30790fd6e485c258c97d957f1c8a8bbfad22945a12578aba219',
 'borrowed-actual-imports-bindings.json':'6b0e29d00cf57429278bb0416c62f8642c15738a80c61bd4e0dd0b31513c2659',
 'borrowed-full-owned-pp1e6.log':'85f7706c43f96abd18118ea736cd84edba0adf4f29d3bc466f4d5fa400fbefea',
 'borrowed-full-owned-pp1e6-DECLARATION_TYPES_AXIOMS.json':'78623bd1c9177a48a5e01ca29319af8810f90a96db3141f9c4b8c042c80725ba',
 'borrowed-full-owned-pp1e6-INVENTORY_NAME_SET_CHECK.json':'d09e59495ca43baf80c1345547ed228a84c40c1a228eedc22aecad784b2ca1fb',
 'VALIDATION_RESULTS.json':'ade84ebedce349c76b22231d43c23fb1a91fe567fbd147d05ffcf151e08341ef',
 'driver-unused-ring-resume.py':'25898c28343725f82bce031e37946193fd0d6e8f87c76a2c356e2c0340dabfc8',
 'runtime-evidence/state.json':'06cb48eee532a98c9b2223d506aeb1c5769c1d8cb8eaea7a9047b7b2950fe529',
}
for n,h in old_receipts.items():preserve(oldout/n,h)
old_runtime=json.loads((oldout/'runtime-evidence/state.json').read_text())
for mapping in ['runtime_sha256','input_sha256','action_script_sha256']:
 for p,h in old_runtime[mapping].items():preserve(p,h)
preflight=oldbase/'SUPPLY_PREFLIGHT.json'
preserve(preflight,'b100d10909740f412bb151a92273fc02e7c924277f01c4ca3765dad0ec8e20f2')
pre=json.loads(preflight.read_text())
old_supply=json.loads((oldout/'SUPPLY_QUALIFICATION.json').read_text())
old_borrows=json.loads((oldout/'BORROWED_OBJECTS.json').read_text())
old_inputs=json.loads((oldout/'borrowed-actual-imports-bindings.json').read_text())
assert old_supply['status']=='PASS_CURRENT_P3_BOUND_IMPORTS_NAMED_KERNEL_FULL_OWNED'
assert len(old_borrows)==18 and old_supply['borrowed_modules']==sorted(old_borrows)==old_inputs['roots']
assert old_supply['owned_count']==394 and old_supply['new_manuscript_credit']==0 and old_supply['source_recompilations']==0
assert old_supply['borrowed_object_records_sha256']==sha(oldout/'BORROWED_OBJECTS.json')
assert old_supply['actual_import_bindings_sha256']==sha(oldout/'borrowed-actual-imports-bindings.json')
assert old_supply['named_kernel']['exit_code']==old_supply['full_owned']['exit_code']==0
for key in ['named_kernel','full_owned']:
 rec=old_supply[key];assert not rec['forbidden_source_calls'];preserve(rec['log_path'],rec['log_sha256'])
assert old_supply['named_kernel']['command'][-18:]==sorted(old_borrows)
replayed=[l.removeprefix('replaying ')for l in P(old_supply['named_kernel']['log_path']).read_text().splitlines()if l.startswith('replaying ')]
assert len(replayed)==len(set(replayed))==18 and set(replayed)==set(old_borrows)
assert old_supply['observed_axioms']==['Classical.choice','Quot.sound','propext']
assert len(json.loads((oldout/'borrowed-full-owned-pp1e6-DECLARATION_TYPES_AXIOMS.json').read_text()))==394
old_by_part={}
for i,part in enumerate(old_inputs['parts']):
 p=P(part['identity']['path']);expected=part['identity'];s=part['stat_snapshot']
 assert stamp(p)==s and p.stat().st_size==expected['bytes'] and sha(p)==expected['sha256'],('Old qualified input changed',str(p))
 assert stamp(p)==s;cache_before[str(p)]=s
 key=(part['module'],part['facet']);assert key not in old_by_part;old_by_part[key]=part
 if i%4000==0:print(json.dumps({'stage':'old-qualified-input-byte-stability','checked_parts':i,'total':len(old_inputs['parts']),'new_proof_credit':0}),flush=True)
assert len(old_by_part)==old_inputs['part_count']==21278
borrows={}
for mod,r in old_borrows.items():
 assert set(r['direct_project_imports'])<=set(old_borrows)
 for key in ['source','original_source']:
  assert preserve(r[key],r['source_sha256'])['bytes']==r['source_bytes']
 for key in ['object','original_object']:
  assert preserve(r[key],r['object_sha256'])['bytes']==r['object_bytes']
 assert re.findall(r'^import\s+(ImbalancedChen\.\S+)',P(r['source']).read_text(),re.M)==r['direct_project_imports']
 dest=lib/(mod.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(P(r['object']).resolve())
 new=dict(r);new['object']=str(dest);new['reused_qualified_object']=r['object'];new['new_source_compilation']=False;borrows[mod]=new
for m in source_imports:
 if m.startswith('ImbalancedChen.'):assert m in borrows
save(out/'BORROWED_OBJECTS.json',borrows)
save(out/'SOURCE_INPUT.json',{'module':target,'blob':source_blob,'sha256':source_sha,'bytes':len(source),'lines':len(source.decode().splitlines()),'exact_direct_imports':source_imports,'normal_compile_allowed_for':[target],'old_selected_source_blob':'1c2991fe16c4c35cc73673a52302a2e5d869dea8','double_literal_review_blob':'c563c724587eb817e940c574088eff71748a16ab','independent_review_blob':'bbc1fdc6035ac7d7606619aa96c134e977e530af','no_new_definition_alias_or_hypothesis':True})
for name,rec in pre['p3_project_configuration'].items():
 original=P('/workspace/goldbach-p3')/name;preserve(original,rec['sha256'])
 (root/name).write_bytes(original.read_bytes())
config=tomllib.loads((root/'lakefile.toml').read_text());assert config['lean_lib']==[{'name':'ImbalancedChen'}]
scope='roots = '+json.dumps([target])+'\nglobs = '+json.dumps([target])+'\n'
text=(root/'lakefile.toml').read_text();assert text.count('name = "ImbalancedChen"\n')==1
(root/'lakefile.toml').write_text(text.replace('name = "ImbalancedChen"\n','name = "ImbalancedChen"\n'+scope))
new=tomllib.loads((root/'lakefile.toml').read_text());new['lean_lib'][0].pop('roots');new['lean_lib'][0].pop('globs');assert new==config
(root/'.lake/packages').symlink_to('/workspace/goldbach-p3/.lake/packages',target_is_directory=True)
configs={str(root/n):sha(root/n)for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
save(out/'CONFIGURATION_ADAPTATION.json',{'original':pre['p3_project_configuration'],'changed_only':{'lean_lib.roots':[target],'lean_lib.globs':[target]},'receiver':configs,'borrowed_objects_are_read_only_symlinks_to_original_qualified_inputs':True})
(base/'original-tools').mkdir()
tools_expected={}
for path,h in pre['original_runtime']['tools'].items():
 preserve(path,h);dest=base/'original-tools'/P(path).name;shutil.copyfile(path,dest);assert sha(dest)==h;tools_expected[str(dest)]=h
GUARD=base/'original-tools/ci_runtime_guard.py'
RUNNER=base/'original-tools/run_guarded.py'
OWNED=base/'original-tools/validate_member_roots_owned.py'
PIN='leanprover/lean4:v4.33.0-rc1';LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux');TOOL_LIB=(TC/'lib/lean').resolve()
runtime_parent=base/'runtime';runtime_parent.mkdir()
base_env=os.environ.copy()
for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR=str(oldbase/'lean-action'),GITHUB_ENV=str(out/'runtime.env'),GITHUB_PATH=str(out/'runtime.path'))
base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
setup_cmd=['python3',str(GUARD),'setup','--evidence',str(out/'runtime-evidence')]
with (out/'runtime-setup.log').open('xb')as f:res=subprocess.run(setup_cmd,cwd=root,env=base_env,stdout=f,stderr=subprocess.STDOUT)
save(out/'runtime-setup-process.json',{'command':setup_cmd,'cwd':str(root),'exit_code':res.returncode,'log_sha256':sha(out/'runtime-setup.log')})
assert res.returncode==0,'Original guard setup failed; inspect runtime-setup.log'
state_path=out/'runtime-evidence/state.json';state=json.loads(state_path.read_text());state_sha=sha(state_path);guardlog=P(state['log'])
assert state['policy']=='Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2'
assert state['action_commit']=='f061402b660e0c34644504b324e830f2991d4865'
assert len(state['action_script_sha256'])==5
runprefix=['python3',str(RUNNER),'--state',str(state_path)]
spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED)
auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
mods=[target]
package_revisions={r['name']:r['rev']for r in json.loads((root/'lake-manifest.json').read_text())['packages']}
package_bindings={}
for part in old_inputs['parts']:
 if part['authority']=='actual_pinned_mathlib_package':
  provider=part['provider'];pkg=P(provider['checkout'])
  if str(pkg)not in package_bindings:
   git=lambda *args:subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
   assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and git('rev-parse','HEAD')==package_revisions[provider['name']]==provider['revision']
   package_bindings[str(pkg)]={k:provider[k]for k in ['name','revision','checkout']}
reuse={'schema':'p29_gate_reuse_existing_18_supply_qualification_v1','status':'REUSED_PRIOR_PASS_BYTES_STABLE_NO_REQUALIFICATION','original_receiver_root':str(oldbase),'original_evidence_archive_sha256':'06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f','original_receipts':{str(oldout/n):h for n,h in old_receipts.items()},'original_supply_receipt':old_supply,'old_qualified_module_count':18,'old_qualified_owned_count':394,'actual_old_input_parts_rehashed_unchanged':len(old_by_part),'new_supplier_source_compilations':0,'new_supplier_named_kernel_replays':0,'new_supplier_owned_replays':0,'new_proof_credit':0,'new_receiver_borrowed_map_sha256':sha(out/'BORROWED_OBJECTS.json'),'original_guard_runner_validator_unchanged':tools_expected}
save(out/'REUSED_SUPPLY_QUALIFICATION.json',reuse)
print(json.dumps({'stage':'existing-supply-reused','modules':18,'old_owned':394,'new_supplier_replays':0,'new_supplier_source_compilations':0}),flush=True)


AUDIT_TEMPLATE='import Lean\nopen Lean\ndef p29ResolvedImports : IO Unit := do\n  initSearchPath (← findSysroot)\n  let names : Array Name := TARGET_MODULE_NAMES\n  let env ← importModules (names.map fun n => { module := n }) {}\n  for idx in [:env.header.modules.size] do\n    let mod := env.header.modules[idx]!\n    let data := env.header.moduleData[idx]!\n    let p ← findOLean mod.module\n    let mut parts : Array System.FilePath := #[p]\n    if data.isModule then\n      parts := parts.push (OLeanLevel.server.adjustFileName p)\n      parts := parts.push (OLeanLevel.private.adjustFileName p)\n    let irSig := p.withExtension "ir.sig"\n    if ← irSig.pathExists then\n      parts := parts.push irSig\n      parts := parts.push (p.withExtension "ir")\n    let partRows ← parts.mapM fun q => do\n      let resolved ← IO.FS.realPath q\n      return Json.mkObj [\n        ("path", toJson q.toString),\n        ("resolved_path", toJson resolved.toString)]\n    IO.println ("P29_ACTUAL_IMPORT " ++ (Json.mkObj [\n      ("module", toJson mod.module.toString),\n      ("is_module", toJson data.isModule),\n      ("direct_imports", toJson (data.imports.map fun i => i.module.toString)),\n      ("parts", toJson partRows)]).compress)\n#eval p29ResolvedImports\n'

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

def compile_audit_text(module_names):
 names='#['+', '.join(chr(96)+m for m in module_names)+']'
 return AUDIT_TEMPLATE.replace('TARGET_MODULE_NAMES',names).encode()

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

def actual_inputs(label,roots,production=None):
 production=production or {}
 code=compile_audit_text(roots);(out/(label+'.lean')).write_bytes(code)
 process=stage(label,runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin'],stdin=code,allow_audit=True)
 rows=[json.loads(line[len('P29_ACTUAL_IMPORT '):])for line in (out/(label+'.log')).read_text().splitlines()if line.startswith('P29_ACTUAL_IMPORT ')]
 assert rows and len(rows)==len({r['module']for r in rows})and set(roots)<={r['module']for r in rows}
 actual={r['module']:r for r in rows};records=[];counts={};by_facet={}
 for row in rows:
  m=row['module'];assert not m.startswith(('MathlibNt.','PrimeNumberTheoremAnd.','Architect.')),('Unexpected research input',m)
  if m.startswith('ImbalancedChen.'):assert m in borrows or m==target,('Unregistered project module',m)
  for part in row['parts']:
   p=P(part['resolved_path']);requested=P(part['path']);st=stamp(p)
   leaf=m.rsplit('.',1)[-1]
   assert p.name.startswith(leaf+'.')
   facet=p.name[len(leaf):];assert facet in ['.olean','.olean.server','.olean.private','.ir.sig','.ir']
   expected=P(m.replace('.','/')+facet)
   if m in borrows:
    old=borrows[m];assert facet=='.olean'and p.resolve()==P(old['object']).resolve()
    digest=sha(p);assert digest==old['object_sha256']and st[2]==old['object_bytes']
    authority=old['authority'];provider={'original_object':old['original_object']}
   elif m==target:
    assert str(p)in production and production[str(p)]['sha256']==sha(p)
    digest=sha(p);authority='current_normal_output';provider={'normal_source_sha256':source_sha}
   elif p.is_relative_to(TOOL_LIB):
    assert p.relative_to(TOOL_LIB)==expected
    digest=sha(p);authority='actual_pinned_lean_release';provider={'lean_commit':LEAN_COMMIT,'toolchain':PIN,'relative_artifact':str(expected)}
   else:
    assert p.parts[-len(expected.parts):]==expected.parts,('Module/path mismatch',m,p)
    libroot=p.parents[len(expected.parts)-1];assert libroot.parts[-4:]==('.lake','build','lib','lean')
    pkg=libroot.parents[3];name=pkg.name
    assert name in package_revisions and name not in ['goldbach','LeanArchitect'],('Unexpected package supplier',m,pkg)
    if str(pkg)not in package_bindings:
     git=lambda *args:subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
     assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and git('rev-parse','HEAD')==package_revisions[name]
     package_bindings[str(pkg)]={'name':name,'revision':package_revisions[name],'checkout':str(pkg)}
    digest=sha(p);authority='actual_pinned_mathlib_package';provider={**package_bindings[str(pkg)],'relative_artifact':str(expected)}
   assert stamp(p)==st,('Input changed during hash',p)
   if str(p)in cache_before:assert stamp(p)==cache_before[str(p)],('Previously bound input changed',p)
   else:cache_before[str(p)]=st
   records.append({'module':m,'facet':facet,'identity':{'path':str(p),'bytes':st[2],'sha256':digest},'requested_path':str(requested),'stat_snapshot':st,'authority':authority,'provider':provider})
   counts[authority]=counts.get(authority,0)+1
   assert (m,facet)not in by_facet;by_facet[(m,facet)]=digest
 for m in roots:
  if m in borrows:
   actualdeps={n for n in actual[m]['direct_imports']if n.startswith('ImbalancedChen.')}
   assert actualdeps==set(borrows[m]['direct_project_imports']),(m,actualdeps,borrows[m]['direct_project_imports'])
 for m,r in borrows.items():
  if m not in actual:continue
  for dep,h in r['producer'].get('deps',{}).items():assert by_facet[(dep,'.olean')]==h
 data={'schema':'p29_unit_tail_actual_input_parts_v1','roots':roots,'module_count':len(rows),'part_count':len(records),'counts':counts,'actual_modules':rows,'parts':records,'loading_api':'Lean.importModules; Lean.findOLean; actual module header and default private/server/IR parts','old_vs_new_standard_part_byte_equality_claim':False,'fresh_whole_import_replay_claim':False}
 save(out/(label+'-bindings.json'),data);return data

def stable():
 assert all(sha(p)==h for p,h in configs.items())
 assert sha(state_path)==state_sha
 assert all(sha(p)==h for p,h in tools_expected.items())
 assert all(P(p).stat().st_size==r['bytes']and sha(p)==r['sha256']for p,r in protected.items())
 assert all(P(p).is_file()and stamp(p)==s for p,s in cache_before.items())
 assert all(sha(r['object'])==r['object_sha256']and sha(r['source'])==r['source_sha256']for r in borrows.values())

def source_outputs():
 paths=[src,lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]
 return {str(p):{'bytes':p.stat().st_size,'sha256':sha(p)}for p in paths}

def bind_existing_qualification(data,allow_target=False):
 used=[]
 for part in data['parts']:
  if part['module']==target:
   assert allow_target
   continue
  key=(part['module'],part['facet'])
  assert key in old_by_part,('Input was not in the accepted qualification',key)
  old=old_by_part[key]
  assert part['identity']==old['identity'],('Qualified input identity differs',key,part['identity'],old['identity'])
  assert part['stat_snapshot']==old['stat_snapshot'],('Qualified input stat differs',key)
  used.append(key)
 original_modules={r['module']:r for r in old_inputs['actual_modules']}
 for row in data['actual_modules']:
  if row['module']==target:
   assert allow_target
   assert [m for m in row['direct_imports']if m!='Init']==source_imports
  else:
   old=original_modules[row['module']]
   assert row['is_module']==old['is_module'] and row['direct_imports']==old['direct_imports']
 return len(used)
try:
 stage('runtime-initial-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe'])
 save(out/'INITIAL_RUNTIME_REPORT_PRESERVED.json',json.loads((out/'runtime-evidence/audit.json').read_text()))
 stage('pinned-lean-version',runprefix+['lake','env','lean','--version'])
 version=(out/'pinned-lean-version.log').read_text()
 assert 'version 4.33.0-rc1,'in version and 'commit '+LEAN_COMMIT+','in version
 stage('pinned-lean-prefix',runprefix+['lake','env','lean','--print-prefix'])
 assert (out/'pinned-lean-prefix.log').read_text().strip()==state['shadow']
 shadow=P(state['shadow']);assert (shadow/'lib').is_symlink()and(shadow/'lib/lean').resolve()==TOOL_LIB
 assert P(state['realbin']).resolve()==(TC/'bin').resolve()
 for name,copy in [('lean','lean-runtime'),('lake','lake')]:
  p=TC/'bin'/name;q=shadow/'bin'/copy
  assert sha(p)==sha(q)==state['runtime_sha256'][str(p)]==state['runtime_sha256'][str(q)]
 before=actual_inputs('gate-direct-imports',source_imports)
 bound_before=bind_existing_qualification(before)
 expected_project=set(m for m in source_imports if m.startswith('ImbalancedChen.'))
 pending=list(expected_project)
 while pending:
  m=pending.pop()
  for dep in borrows[m]['direct_project_imports']:
   if dep not in expected_project:expected_project.add(dep);pending.append(dep)
 actual_project={r['module']for r in before['actual_modules']if r['module'].startswith('ImbalancedChen.')}
 assert actual_project==expected_project
 stable()
 save(out/'PRE_NORMAL_INPUT_BINDING.json',{'source_git_blob':source_blob,'source_sha256':source_sha,'direct_imports':source_imports,'actual_import_bindings_sha256':sha(out/'gate-direct-imports-bindings.json'),'same_existing_qualification_parts':bound_before,'actual_project_modules':sorted(actual_project),'reused_original_18_supply_receipt_sha256':sha(oldout/'SUPPLY_QUALIFICATION.json'),'current_reuse_receipt_sha256':sha(out/'REUSED_SUPPLY_QUALIFICATION.json'),'new_supplier_replays':0,'new_supplier_source_compilations':0})
 normal_cmd=runprefix+['lake','env','lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(lib/(target.replace('.','/')+'.olean')),'-i',str(lib/(target.replace('.','/')+'.ilean')),str(src)]
 normal=stage('normal-build',normal_cmd,allow_sources={str(src.resolve())},timeout=900)
 produced=source_outputs();save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',produced)
 after=actual_inputs('consumer-actual-imports',[target],produced)
 bound_after=bind_existing_qualification(after,allow_target=True)
 assert bound_after==bound_before
 assert {r['module']for r in after['actual_modules']}=={r['module']for r in before['actual_modules']}|{target}
 kernel=named_kernel('named-kernel',[target])
 owned,decls,inventory,axioms=full_owned('full-owned',[target])
 stage('runtime-final-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe','--require-source'])
 stable();assert source_outputs()==produced and sha(src)==source_sha
 save(out/'SOURCE_AND_OUTPUTS_AFTER.json',produced)
 all_commands=[json.loads(l)for l in guardlog.read_text().splitlines()if l]
 lean_sources=[str(P(r['cwd'])/a)if not P(a).is_absolute()else a for r in all_commands if r.get('tool')=='lean' for a in r.get('input_args',[])if a.endswith('.lean')]
 assert lean_sources==[str(src)],lean_sources
 assert not list(lib.glob(target.replace('.','/')+'.trace')) and not list(lib.glob(target.replace('.','/')+'.setup.json'))
 result={'schema':'p29_gate_affine_P3_normal_named_kernel_full_owned_v1','result':'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED','module':target,'source_git_blob':source_blob,'source_sha256':source_sha,'source_bytes':len(source),'normal':normal,'kernel':kernel,'owned':owned,'owned_count':len(decls),'inventory':inventory,'observed_axioms':axioms,'all_owned_private_generated_types_and_universes':True,'actual_input_modules':after['module_count'],'actual_input_parts':after['part_count'],'actual_input_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'pre_normal_import_bindings_sha256':sha(out/'gate-direct-imports-bindings.json'),'existing_qualified_input_parts_used':bound_after,'original_guard_runner_validator_unchanged':tools_expected,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'normal_source_invocations':lean_sources,'borrowed_source_recompilations':0,'borrowed_module_count':18,'borrowed_modules_actually_used':sorted(expected_project),'borrowed_new_kernel_replays':0,'borrowed_new_owned_replays':0,'original_supply_receipt_sha256':sha(oldout/'SUPPLY_QUALIFICATION.json'),'current_supply_reuse_receipt_sha256':sha(out/'REUSED_SUPPLY_QUALIFICATION.json'),'direct_Lean_outputs':['.olean','.ilean'],'no_Lake_trace_or_setup_created':True,'no_existing_Unit_evidence_modified':True,'full_P2_9_complete':False,'whole_standard_import_kernel_replay_claim':False,'scope':'Original nonproduct Gamma5 gate affine forms, omitted-slot witnesses, and the original proper-strip alternative, with the exact actualPrimeTupleLog and properStrip definitions expanded literally. No new mathematical hypothesis, coordinate carrier, source restriction, additive-prime condition or signed-PP input.'}
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','module','owned_count','observed_axioms','actual_input_modules','actual_input_parts']}),flush=True)
except Exception as e:
 partial={str(p):{'bytes':p.stat().st_size,'sha256':sha(p)}for p in [src,lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]if p.is_file()}
 failure={'schema':'p29_gate_affine_P3_gate_failure_v1','root':str(root),'evidence':str(out),'source_git_blob':source_blob,'source_sha256':source_sha,'error':str(e),'traceback':traceback.format_exc(),'completed_stages':[r['stage']for r in runs],'changed_protected_parts':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s],'partial_target_outputs_preserved':partial,'existing_supply_qualification_reused':True,'supplier_recompilations':0,'supplier_kernel_owned_replays':0}
 save(out/'FAILURE.json',failure);print(json.dumps(failure),flush=True);raise
members={}
for p in out.rglob('*'):
 if p.is_file():
  assert not p.is_symlink();members['verification/'+str(p.relative_to(out))]=p
for p in [src,root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json',lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]:
 assert p.is_file()and not p.is_symlink();members['project/'+str(p.relative_to(root))]=p
for p in (base/'original-tools').iterdir():members['original-tools/'+p.name]=p
manifest={k:{'bytes':p.stat().st_size,'sha256':sha(p)}for k,p in members.items()}
save(base/'FILE_MANIFEST.json',{'schema':'p29_gate_complete_current_receiver_evidence_v1','files':manifest,'excludes':['FILE_MANIFEST.json'],'borrowed_original_18_evidence_archive_sha256':'06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f','borrowed_symlinks_not_packaged_as_new_objects':True,'no_old_supplier_source_kernel_owned_replay':True})
members['FILE_MANIFEST.json']=base/'FILE_MANIFEST.json'
archive=base/'qualified-gate-affine.tar.xz'
with tarfile.open(archive,'w:xz',preset=6)as t:
 for name,p in sorted(members.items()):t.add(p,arcname=name,recursive=False)
meta={'path':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),'members':len(members),'manifest_sha256':sha(base/'FILE_MANIFEST.json'),'new_module':target,'new_owned_count':len(decls),'old_supplier_owned_count_reused_without_replay':394}
save(base/'ARCHIVE_TRANSPORT.json',meta);print('P29_ARCHIVE '+json.dumps(meta),flush=True)
