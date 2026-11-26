import pathlib,os,sys,json,hashlib,subprocess,time,signal,datetime,traceback,shutil,tomllib,importlib.util,urllib.request,base64,re,tarfile
P=pathlib.Path
sys.dont_write_bytecode=True
base=P('/workspace/p29-gate-affine-20261126-ba9b1989')
oldbase=P('/workspace/p29-unit-tail-20261126-8131f7d6');oldout=oldbase/'verification'
root=base/'project';out=base/'verification'
assert root.is_dir()and out.is_dir()
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
assert sha(out/'driver.py')=='a9b7b6685df439c8007cfdf1ee4b43b6dde854aa9bee0e1c2d4996b3805bf86b'
assert not(out/'driver-constructor-if-repair-v2.py').exists(),'Do not repeat this target-only continuation.'
(out/'driver-constructor-if-repair-v2.py').write_text(SOURCE_TEXT)
target='ImbalancedChen.P2FiniteMarkedGamma5GateAffine'
prior_source_blob='9db6ca0e6a53ff63272f092d4218b6135da85fae'
prior_source_sha='2f9a610f56e0e9bbfc01fbefa3316c3cd1444151140c14fa8ab198a38ffb4022'
source_blob='fb1ab9c164ecd705653903a57b9ee53838303de9'
source_sha='18967fcc3ced75318d5b8d7e6ee40153b30d6dfc8678527a6f37753550f9a6db'
src=root/(target.replace('.','/')+'.lean');prior_source=src.read_bytes()
assert len(prior_source)==10506 and sha(src)==prior_source_sha
lib=root/'.lake/build/lib/lean'
assert not(lib/(target.replace('.','/')+'.olean')).exists()
assert not(lib/(target.replace('.','/')+'.ilean')).exists()
protected={};cache_before={};runs=[]
def preserve(p,expected=None):
 p=P(p);s=stamp(p);d=sha(p);assert stamp(p)==s
 if expected is not None:assert d==expected,(str(p),'hash mismatch')
 row={'bytes':s[2],'sha256':d};protected[str(p)]=row;cache_before[str(p)]=s;return row
fixed_gate_files={
 'driver.py':'a9b7b6685df439c8007cfdf1ee4b43b6dde854aa9bee0e1c2d4996b3805bf86b',
 'FAILURE.json':'68674ddedbe3bcacfd6985d4b7d9afc8b2c9bc8771682a1cadd7a44185db6c1a',
 'OUTER_FAILURE.json':'f959c205aa3e883672df97123815663c3661c84c3d0ebf7a44a28204a6ecccd1',
 'normal-build-process.json':'716ffffa428d23cbd025fd5614119c31c381061bc5d9d1c8c0d15769fdf3d4bf',
 'normal-build.log':'ecac80b2a7eb89523a69b9b4eab6c65eca5dc29f91c89c268613bbfcc4fd3409',
 'PRE_NORMAL_INPUT_BINDING.json':'533dea9ae573c462a9a1442d2f8d19719525fa4a8146fea58d3c2a044bae5c4b',
 'REUSED_SUPPLY_QUALIFICATION.json':'464a86b1c9b262cb87f723d32e944aa6995a600846c5405b387bbd6f0a38d12e',
 'gate-direct-imports-bindings.json':'5732331ab4bddeb3f505964f5d2fe7d4b87e3d50269f2af14fdffdd69e18e722',
 'BORROWED_OBJECTS.json':'7cbfae9627ac8d0ad83a33fa7de1362643ebe40b03fbf12886adae37def938f5',
 'runtime-evidence/state.json':'c3a5b76d753beacc00acc0a346cf9c891d9173693e934c172a938ea5eb77ae8b',
 'INITIAL_RUNTIME_REPORT_PRESERVED.json':'fa218d89476014e9f3055c36fec7fed5738453338fda1aeb1bc9d98a28cd4da8',
}
fixed_gate_files.update({
 'driver-proof-repair-v1.py':'cdc7420eb1052cca1575d388286053002ca3fbf0c6dd5ff02c0c775f40d6d295',
 'FAILURE-proof-repair-v1.json':'89689c946aa2353556e25cb5081d5a66342a148df4711121657f1a16a6b10bd2',
 'OUTER_FAILURE-proof-repair-v1.json':'8ae07c28425adb91367471938490c8ef7fbef5fc8cde35ba6eead473ac22c456',
 'normal-build-proof-repair-v1-process.json':'66b9509007a6db4ef0e4b207cf081c886ac3929b3c3898cd527e9d814e683b05',
 'normal-build-proof-repair-v1.log':'5d2382d95be6c81c60fd239bae25ba3f68ece85f44402135710edfcb0b944734',
 'SOURCE_REPAIR_AND_INPUT.json':'06366dcf8bdf449cddbf740e31ed0e9ef52e90f11d17694ab55f1f115ced47c0',
 'failed-target-first-normal/SOURCE_COMMAND_BINDING.json':'ac4102c0c12bf8dd1972c43fa25504ddc4065530bb3fb36f43a844d6f0808808',
 'failed-target-first-normal/GateAffine-first-normal.lean':'ba9b1989c42a681de23ad448749c0f8a1a10ae77160dabc512f664b65cfa2b55',
 'PROOF_ONLY_REPAIR_REVIEW.json':'47573019907a15060661812358cc358486ae5f33494912259257fb818092201a',
})
for n,h in fixed_gate_files.items():preserve(out/n,h)
reuse=json.loads((out/'REUSED_SUPPLY_QUALIFICATION.json').read_text())
assert reuse['status']=='REUSED_PRIOR_PASS_BYTES_STABLE_NO_REQUALIFICATION'
assert reuse['old_qualified_module_count']==18 and reuse['old_qualified_owned_count']==394
assert reuse['new_supplier_source_compilations']==reuse['new_supplier_named_kernel_replays']==reuse['new_supplier_owned_replays']==0
for p,h in reuse['original_receipts'].items():preserve(p,h)
old_supply=json.loads((oldout/'SUPPLY_QUALIFICATION.json').read_text())
assert old_supply==reuse['original_supply_receipt']
for key in ['named_kernel','full_owned']:
 rec=old_supply[key];assert rec['exit_code']==0 and not rec['forbidden_source_calls'];preserve(rec['log_path'],rec['log_sha256'])
old_runtime=json.loads((oldout/'runtime-evidence/state.json').read_text())
for mapping in ['runtime_sha256','input_sha256','action_script_sha256']:
 for p,h in old_runtime[mapping].items():preserve(p,h)
preflight=oldbase/'SUPPLY_PREFLIGHT.json';preserve(preflight,'b100d10909740f412bb151a92273fc02e7c924277f01c4ca3765dad0ec8e20f2');pre=json.loads(preflight.read_text())
borrows=json.loads((out/'BORROWED_OBJECTS.json').read_text());assert len(borrows)==18 and old_supply['borrowed_modules']==sorted(borrows)
for mod,r in borrows.items():
 for key in ['source','original_source']:
  assert preserve(r[key],r['source_sha256'])['bytes']==r['source_bytes']
 for key in ['object','original_object','reused_qualified_object']:
  assert preserve(r[key],r['object_sha256'])['bytes']==r['object_bytes']
 assert P(r['object']).is_symlink()and P(r['object']).resolve()==P(r['reused_qualified_object']).resolve()
old_inputs=json.loads((oldout/'borrowed-actual-imports-bindings.json').read_text());old_by_part={}
for i,part in enumerate(old_inputs['parts']):
 p=P(part['identity']['path']);expected=part['identity'];s=part['stat_snapshot']
 assert stamp(p)==s and p.stat().st_size==expected['bytes']and sha(p)==expected['sha256'],('Old qualified input changed',str(p))
 assert stamp(p)==s;cache_before[str(p)]=s;key=(part['module'],part['facet']);assert key not in old_by_part;old_by_part[key]=part
 if i%4000==0:print(json.dumps({'stage':'resume-input-byte-stability','checked_parts':i,'total':len(old_inputs['parts']),'new_supplier_replays':0}),flush=True)
assert len(old_by_part)==21278
before=json.loads((out/'gate-direct-imports-bindings.json').read_text())
pre_normal=json.loads((out/'PRE_NORMAL_INPUT_BINDING.json').read_text())
assert pre_normal['source_git_blob']=='fddfeda6a91675472e8fb05dd8301f379bd1d111' and pre_normal['source_sha256']=='ba9b1989c42a681de23ad448749c0f8a1a10ae77160dabc512f664b65cfa2b55'
assert pre_normal['actual_import_bindings_sha256']==sha(out/'gate-direct-imports-bindings.json')
assert pre_normal['reused_original_18_supply_receipt_sha256']==sha(oldout/'SUPPLY_QUALIFICATION.json')
assert pre_normal['current_reuse_receipt_sha256']==sha(out/'REUSED_SUPPLY_QUALIFICATION.json')
configs=json.loads((out/'CONFIGURATION_ADAPTATION.json').read_text())['receiver']
for p,h in configs.items():preserve(p,h)
GUARD=base/'original-tools/ci_runtime_guard.py';RUNNER=base/'original-tools/run_guarded.py';OWNED=base/'original-tools/validate_member_roots_owned.py'
tools_expected=reuse['original_guard_runner_validator_unchanged']
for p,h in tools_expected.items():preserve(p,h)
for p,h in pre['original_runtime']['tools'].items():preserve(p,h)
PIN='leanprover/lean4:v4.33.0-rc1';LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux');TOOL_LIB=(TC/'lib/lean').resolve()
runtime_parent=base/'runtime';base_env=os.environ.copy()
for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR=str(oldbase/'lean-action'),GITHUB_ENV=str(out/'runtime.env'),GITHUB_PATH=str(out/'runtime.path'))
base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
state_path=out/'runtime-evidence/state.json';state=json.loads(state_path.read_text());state_sha=sha(state_path);guardlog=P(state['log'])
assert state['policy']=='Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2'
assert state['action_commit']=='f061402b660e0c34644504b324e830f2991d4865'and len(state['action_script_sha256'])==5
for mapping in ['runtime_sha256','input_sha256','action_script_sha256']:
 for p,h in state[mapping].items():preserve(p,h)
initial=json.loads((out/'INITIAL_RUNTIME_REPORT_PRESERVED.json').read_text());assert initial['status']=='PASS_RUNTIME_GUARD_ONLY'and initial['state_sha256']==state_sha
assert initial==json.loads((out/'runtime-evidence/audit.json').read_text())
runprefix=['python3',str(RUNNER),'--state',str(state_path)]
spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED);auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
mods=[target];package_revisions={r['name']:r['rev']for r in json.loads((root/'lake-manifest.json').read_text())['packages']};package_bindings={}
for part in old_inputs['parts']:
 if part['authority']=='actual_pinned_mathlib_package':
  provider=part['provider'];pkg=P(provider['checkout'])
  if str(pkg)not in package_bindings:
   git=lambda *args:subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
   assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and git('rev-parse','HEAD')==package_revisions[provider['name']]==provider['revision']
   package_bindings[str(pkg)]={k:provider[k]for k in ['name','revision','checkout']}
completed={}
for label in ['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','gate-direct-imports']:
 p=out/(label+'-process.json');rec=json.loads(p.read_text());assert rec['exit_code']==0 and not rec['forbidden_source_calls']and rec['cwd']==str(root)
 preserve(rec['log_path'],rec['log_sha256']);preserve(p);completed[label]=rec
normal_previous=json.loads((out/'normal-build-proof-repair-v1-process.json').read_text())
assert normal_previous['exit_code']==1 and not normal_previous['forbidden_source_calls']and normal_previous['log_sha256']==sha(out/'normal-build-proof-repair-v1.log')
assert normal_previous['command']==runprefix+['lake','env','lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(lib/(target.replace('.','/')+'.olean')),'-i',str(lib/(target.replace('.','/')+'.ilean')),str(src)]
source=get_blob(source_blob);assert len(source)==10694 and hashlib.sha256(source).hexdigest()==source_sha
review_bytes=get_blob('2986d62b64d21a3dc4bf4d2ffe8f141b09fa091c');assert hashlib.sha256(review_bytes).hexdigest()=='6b77caf129daac09fecc85693012b29654ede33433a89aa921297952d41c1e0a'
review=json.loads(review_bytes);expected=prior_source.decode()
for sub in review['exact_replacements']:
 assert expected.count(sub['old'])==1;expected=expected.replace(sub['old'],sub['new'])
assert expected.encode()==source
def headers(text):
 pattern=re.compile(r'^(?:private )?(?:def|abbrev|theorem)\s+\w+\b',re.M);ms=list(pattern.finditer(text));rows=[]
 for i,m in enumerate(ms):
  block=text[m.start():ms[i+1].start()if i+1<len(ms)else len(text)];rows.append(block[:re.search(r':=|\n  \|',block).start()])
 return rows
assert headers(prior_source.decode())==headers(source.decode())and len(headers(source.decode()))==23
source_imports=re.findall(r'^import\s+(\S+)',source.decode(),re.M)
assert source_imports==re.findall(r'^import\s+(\S+)',prior_source.decode(),re.M)==before['roots']==pre_normal['direct_imports']
failed_dir=out/'failed-target-second-normal';failed_dir.mkdir()
failed_src=failed_dir/'GateAffine-second-normal.lean';failed_src.write_bytes(prior_source);assert sha(failed_src)==prior_source_sha
save(failed_dir/'SOURCE_COMMAND_BINDING.json',{'source_git_blob':prior_source_blob,'source_sha256':prior_source_sha,'source_bytes':len(prior_source),'original_source_path':str(src),'preserved_source_path':str(failed_src),'normal_process':normal_previous,'normal_log_sha256':sha(out/'normal-build-proof-repair-v1.log'),'normal_exit_code':1,'produced_olean':False,'produced_ilean':False})
(out/'CONSTRUCTOR_IF_REPAIR_V2_REVIEW.json').write_bytes(review_bytes)
src.write_bytes(source);assert sha(src)==source_sha
save(out/'SOURCE_REPAIR_AND_INPUT_V2.json',{'schema':'p29_gate_three_constructor_if_only_repair_v2','module':target,'source_git_blob':source_blob,'source_sha256':source_sha,'source_bytes':len(source),'previous_source_git_blob':prior_source_blob,'previous_source_sha256':prior_source_sha,'all_23_statement_and_import_bytes_unchanged':True,'exact_replacement_review_git_blob':'2986d62b64d21a3dc4bf4d2ffe8f141b09fa091c','retained_strict_warningAsError':True,'original_guard_runner_validator_unchanged':tools_expected,'reuse_supply_receipt_sha256':sha(out/'REUSED_SUPPLY_QUALIFICATION.json'),'reuse_pre_normal_imports_sha256':sha(out/'gate-direct-imports-bindings.json'),'no_supplier_source_kernel_owned_or_actual_import_probe_repeated':True,'prior_runtime_and_actual_import_stages_preserved':completed,'borrowed_actual_parts_rehashed_unchanged':len(old_by_part),'failed_target_outputs_existed':False})


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
 assert completed['gate-direct-imports']['stdin_sha256']==hashlib.sha256(compile_audit_text(source_imports)).hexdigest()
 assert (out/'gate-direct-imports.lean').read_bytes()==compile_audit_text(source_imports)
 bound_before=bind_existing_qualification(before)
 assert bound_before==pre_normal['same_existing_qualification_parts']
 expected_project=set(pre_normal['actual_project_modules'])
 assert expected_project=={r['module']for r in before['actual_modules']if r['module'].startswith('ImbalancedChen.')}
 stable()
 print(json.dumps({'stage':'completed-gates-reused','runtime_and_import_probe_reruns':0,'old_supplier_normal_kernel_owned_reruns':0,'only_unfinished_target_normal':target}),flush=True)
 normal_cmd=runprefix+['lake','env','lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(lib/(target.replace('.','/')+'.olean')),'-i',str(lib/(target.replace('.','/')+'.ilean')),str(src)]
 normal=stage('normal-build-constructor-if-repair-v2',normal_cmd,allow_sources={str(src.resolve())},timeout=900)
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
 assert lean_sources==[str(src),str(src),str(src)],lean_sources
 assert not list(lib.glob(target.replace('.','/')+'.trace')) and not list(lib.glob(target.replace('.','/')+'.setup.json'))
 result={'schema':'p29_gate_affine_P3_normal_named_kernel_full_owned_v1','result':'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED','module':target,'source_git_blob':source_blob,'source_sha256':source_sha,'source_bytes':len(source),'normal':normal,'kernel':kernel,'owned':owned,'owned_count':len(decls),'inventory':inventory,'observed_axioms':axioms,'all_owned_private_generated_types_and_universes':True,'actual_input_modules':after['module_count'],'actual_input_parts':after['part_count'],'actual_input_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'pre_normal_import_bindings_sha256':sha(out/'gate-direct-imports-bindings.json'),'existing_qualified_input_parts_used':bound_after,'original_guard_runner_validator_unchanged':tools_expected,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'normal_source_invocations':lean_sources,'successful_normal_source_invocations':1,'failed_normal_source_invocations':2,'first_failed_normal_source_git_blob':'fddfeda6a91675472e8fb05dd8301f379bd1d111','second_failed_normal_source_git_blob':prior_source_blob,'source_repair_record_sha256':sha(out/'SOURCE_REPAIR_AND_INPUT_V2.json'),'borrowed_source_recompilations':0,'borrowed_module_count':18,'borrowed_modules_actually_used':sorted(expected_project),'borrowed_new_kernel_replays':0,'borrowed_new_owned_replays':0,'original_supply_receipt_sha256':sha(oldout/'SUPPLY_QUALIFICATION.json'),'current_supply_reuse_receipt_sha256':sha(out/'REUSED_SUPPLY_QUALIFICATION.json'),'direct_Lean_outputs':['.olean','.ilean'],'no_Lake_trace_or_setup_created':True,'no_existing_Unit_evidence_modified':True,'full_P2_9_complete':False,'whole_standard_import_kernel_replay_claim':False,'scope':'Original nonproduct Gamma5 gate affine forms, omitted-slot witnesses, and the original proper-strip alternative, with the exact actualPrimeTupleLog and properStrip definitions expanded literally. No new mathematical hypothesis, coordinate carrier, source restriction, additive-prime condition or signed-PP input.'}
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','module','owned_count','observed_axioms','actual_input_modules','actual_input_parts']}),flush=True)
except Exception as e:
 partial={str(p):{'bytes':p.stat().st_size,'sha256':sha(p)}for p in [src,lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]if p.is_file()}
 failure={'schema':'p29_gate_affine_P3_gate_failure_v1','root':str(root),'evidence':str(out),'source_git_blob':source_blob,'source_sha256':source_sha,'error':str(e),'traceback':traceback.format_exc(),'completed_stages':[r['stage']for r in runs],'changed_protected_parts':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s],'partial_target_outputs_preserved':partial,'existing_supply_qualification_reused':True,'supplier_recompilations':0,'supplier_kernel_owned_replays':0}
 save(out/'FAILURE-constructor-if-repair-v2.json',failure);print(json.dumps(failure),flush=True);raise
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
