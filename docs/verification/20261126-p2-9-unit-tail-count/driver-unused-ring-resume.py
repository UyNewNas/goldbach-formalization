import pathlib,os,sys,json,hashlib,subprocess,time,signal,datetime,traceback,shutil,tomllib,importlib.util,urllib.request,base64,re,tarfile
P=pathlib.Path
base=P('/workspace/p29-unit-tail-20261126-8131f7d6')
root=base/'project';out=base/'verification'
assert root.is_dir()and out.is_dir()
def sha(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def stamp(p):
 s=P(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def save(p,x):
 p=P(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(x,f,indent=2);f.write('\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
assert sha(out/'driver.py')=='a491b02c371d1998e8d61b1e2598b7f89e15c86915e1a1ff3acf69f8b2219de6'
assert sha(out/'driver-pp1e6-resume.py')=='a333893eebadaa41ebb1cf431c8f187d4fb13db4aa3a286dfef5a25a705f17fd'
assert not(out/'driver-unused-ring-resume.py').exists(),'Do not repeat a submitted continuation.'
(out/'driver-unused-ring-resume.py').write_text(SOURCE_TEXT)
preflight=base/'SUPPLY_PREFLIGHT.json'
assert sha(preflight)=='b100d10909740f412bb151a92273fc02e7c924277f01c4ca3765dad0ec8e20f2'
pre=json.loads(preflight.read_text())
target='ImbalancedChen.P2FiniteMarkedGamma5UnitTailCount'
source_blob='f3c41302fc6253c52445ae6f30fdfd3abc41cc5b'
source_sha='58c33dc5a5ae7747a25848c73253f0664956bc88a22bb130de9d1e3a41e19ae9'
src=root/(target.replace('.','/')+'.lean');source=src.read_bytes()
assert len(source)==7463 and sha(src)==source_sha
lib=root/'.lake/build/lib/lean'
assert not(lib/(target.replace('.','/')+'.olean')).exists()
assert not(lib/(target.replace('.','/')+'.ilean')).exists()
borrows=json.loads((out/'BORROWED_OBJECTS.json').read_text());assert len(borrows)==18
configs=json.loads((out/'CONFIGURATION_ADAPTATION.json').read_text())['receiver']
protected={};cache_before={}
for m,r in borrows.items():
 for key,hashed in [('original_source','source'),('original_object','object')]:
  p=P(r[key]);record={'bytes':r[hashed+'_bytes'],'sha256':r[hashed+'_sha256']}
  assert p.stat().st_size==record['bytes']and sha(p)==record['sha256']
  protected[str(p)]=record;cache_before[str(p)]=stamp(p)
for m,r in pre['power_closure'].items():
 for p,v in r['files'].items():
  assert P(p).stat().st_size==v['bytes']and sha(p)==v['sha256']
  protected[p]={'bytes':v['bytes'],'sha256':v['sha256']};cache_before[p]=stamp(p)
borrowed_imports=json.loads((out/'borrowed-actual-imports-bindings.json').read_text())
assert borrowed_imports['roots']==sorted(borrows)
for part in borrowed_imports['parts']:
 p=P(part['identity']['path']);expected=part['identity'];s=part['stat_snapshot']
 assert stamp(p)==s and p.stat().st_size==expected['bytes']and sha(p)==expected['sha256']
 cache_before[str(p)]=s
GUARD=base/'original-tools/ci_runtime_guard.py'
RUNNER=base/'original-tools/run_guarded.py'
OWNED=base/'original-tools/validate_member_roots_owned.py'
tools_expected=pre['original_runtime']['tools'];assert all(sha(p)==h for p,h in tools_expected.items())
PIN='leanprover/lean4:v4.33.0-rc1';LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux');TOOL_LIB=(TC/'lib/lean').resolve()
runtime_parent=base/'runtime'
base_env=os.environ.copy()
for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR=str(base/'lean-action'),GITHUB_ENV=str(out/'runtime.env'),GITHUB_PATH=str(out/'runtime.path'))
base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
state_path=out/'runtime-evidence/state.json';state=json.loads(state_path.read_text());state_sha=sha(state_path);guardlog=P(state['log'])
assert state['policy']=='Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2'
initial_runtime=json.loads((out/'runtime-evidence/audit.json').read_text())
assert initial_runtime['state_sha256']==state_sha and initial_runtime['status']=='PASS_RUNTIME_GUARD_ONLY'
assert json.loads((out/'INITIAL_RUNTIME_REPORT_PRESERVED.json').read_text())==initial_runtime
for mapping in ['runtime_sha256','input_sha256','action_script_sha256']:
 for p,h in state[mapping].items():assert sha(p)==h
runprefix=['python3',str(RUNNER),'--state',str(state_path)]
runs=[]
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED)
auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
mods=[target]
package_revisions={r['name']:r['rev']for r in json.loads((root/'lake-manifest.json').read_text())['packages']}
package_bindings={}
for part in borrowed_imports['parts']:
 if part['authority']=='actual_pinned_mathlib_package':
  provider=part['provider'];pkg=P(provider['checkout'])
  if str(pkg)not in package_bindings:
   git=lambda *args:subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
   assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and git('rev-parse','HEAD')==package_revisions[provider['name']]==provider['revision']
   package_bindings[str(pkg)]={k:provider[k]for k in ['name','revision','checkout']}
old_stage_labels=['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','borrowed-actual-imports','borrowed-named-kernel','borrowed-full-owned']
old_stages={}
for label in old_stage_labels:
 rec=json.loads((out/(label+'-process.json')).read_text())
 assert rec['exit_code']==0 and rec['cwd']==str(root)and rec['log_sha256']==sha(rec['log_path'])and not rec['forbidden_source_calls']
 old_stages[label]=rec
borrowed_kernel=old_stages['borrowed-named-kernel']
assert borrowed_kernel['command']==runprefix+['lake','env','leanchecker','--verbose',*sorted(borrows)]
replayed=[l.removeprefix('replaying ')for l in (out/'borrowed-named-kernel.log').read_text().splitlines()if l.startswith('replaying ')]
assert len(replayed)==len(set(replayed))==18 and set(replayed)==set(borrows)
assert old_stages['borrowed-actual-imports']['stdin_sha256']==sha(out/'borrowed-actual-imports.lean')
original_audit=auditor.make_audit_code(sorted(borrows)).encode()
assert (out/'borrowed-full-owned.lean').read_bytes()==original_audit
assert old_stages['borrowed-full-owned']['stdin_sha256']==hashlib.sha256(original_audit).hexdigest()
assert sha(out/'borrowed-full-owned.log')=='bcfe0f454cbeb35da6af9c05cd680eafd4909ba6946c224e6d9fb4f08bfa6994'
old_raw=(out/'borrowed-full-owned.log').read_text()
old_rows=[json.loads(l.removeprefix('MEMBER_OWNED_DECL '))for l in old_raw.splitlines()if l.startswith('MEMBER_OWNED_DECL ')]
old_issues=[{'name':r['name'],'module':r['module'],'field':key,'characters':len(r[key]),'ellipsis_count':r[key].count('⋯')+r[key].count('...')}for r in old_rows for key in ['type','type_expression']if '⋯'in r[key]or '...'in r[key]]
assert len(old_rows)==394 and old_issues==[{'name':'ImbalancedChen.P2FiniteMarkedGamma5LogExtension.marginRow.eq_7','module':'ImbalancedChen.P2FiniteMarkedGamma5DerivativeBudget','field':'type','characters':73447,'ellipsis_count':14}]

assert sha(out/'SUPPLY_QUALIFICATION.json')=='1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21'
supply=json.loads((out/'SUPPLY_QUALIFICATION.json').read_text())
assert supply['status']=='PASS_CURRENT_P3_BOUND_IMPORTS_NAMED_KERNEL_FULL_OWNED'
assert supply['borrowed_modules']==sorted(borrows)and supply['owned_count']==394 and supply['new_manuscript_credit']==0 and supply['source_recompilations']==0
assert supply['borrowed_object_records_sha256']==sha(out/'BORROWED_OBJECTS.json')
assert supply['actual_import_bindings_sha256']==sha(out/'borrowed-actual-imports-bindings.json')
assert supply['named_kernel']==borrowed_kernel
borrowed_owned=supply['full_owned'];assert borrowed_owned['exit_code']==0 and borrowed_owned['log_sha256']==sha(borrowed_owned['log_path'])
assert borrowed_owned['stdin_sha256']==hashlib.sha256(original_audit).hexdigest()and (out/'borrowed-full-owned-pp1e6.lean').read_bytes()==original_audit
assert sha(out/'borrowed-full-owned-pp1e6-DECLARATION_TYPES_AXIOMS.json')=='78623bd1c9177a48a5e01ca29319af8810f90a96db3141f9c4b8c042c80725ba'
assert sha(out/'borrowed-full-owned-pp1e6-INVENTORY_NAME_SET_CHECK.json')=='d09e59495ca43baf80c1345547ed228a84c40c1a228eedc22aecad784b2ca1fb'
assert sha(out/'PP_MAX_STEPS_RESOLUTION.json')=='ffc93b5fc45dd4b78e012bcd297556e648ea4ddceee2569aff9627d3899c94e6'
assert sha(out/'normal-build.log')=='bbe762a99135efe276c52ee0c7c5c2a635300aba0cc2e5d8f3de9af040337cf0'
assert sha(out/'normal-build-process.json')=='4b4b99536faa2cfe253b7881f9deab4b6bc83e32434646b31722a1548bf4aff7'
failed_normal=json.loads((out/'normal-build-process.json').read_text())
assert failed_normal['exit_code']==1 and not failed_normal['forbidden_source_calls']and failed_normal['log_sha256']==sha(out/'normal-build.log')
assert failed_normal['command']==runprefix+['lake','env','lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(lib/(target.replace('.','/')+'.olean')),'-i',str(lib/(target.replace('.','/')+'.ilean')),str(src)]
assert len((out/'normal-build.log').read_bytes())==226 and "error: 'ring' tactic does nothing"in (out/'normal-build.log').read_text()
prior_source=source;prior_source_sha=source_sha;prior_source_blob=source_blob
source_blob='5d33cb4e987efc197536d38f132a22834c3d5e46'
source_sha='45136f0a1ff1c46d426851d4d74e1b2b1226da6bea7522e7e31b9603bc609dde'
blob_response=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+source_blob,timeout=45))
assert blob_response['encoding']=='base64'
source=base64.b64decode(blob_response['content'])
assert len(source)==7454 and hashlib.sha256(source).hexdigest()==source_sha
assert hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()==source_blob
old_line=b"      field_simp [h0.ne', (rpow_pos_of_pos h0 saving).ne'] <;> ring"
new_line=b"      field_simp [h0.ne', (rpow_pos_of_pos h0 saving).ne']"
assert prior_source.count(old_line)==1 and prior_source.replace(old_line,new_line)==source
assert re.findall(rb'^import .*$',prior_source,re.M)==re.findall(rb'^import .*$',source,re.M)
failed_dir=out/'failed-target-normal';failed_dir.mkdir()
failed_source=failed_dir/'UnitTailCount-first-normal.lean';failed_source.write_bytes(prior_source)
assert sha(failed_source)==prior_source_sha
save(failed_dir/'SOURCE_COMMAND_BINDING.json',{'source_git_blob':prior_source_blob,'source_sha256':prior_source_sha,'source_bytes':len(prior_source),'original_source_path':str(src),'preserved_source_path':str(failed_source),'normal_process':failed_normal,'normal_log_sha256':sha(out/'normal-build.log'),'normal_exit_code':1,'produced_olean':False,'produced_ilean':False})
src.write_bytes(source)
assert sha(src)==source_sha
save(out/'SOURCE_REPAIR_AND_INPUT.json',{'schema':'p29_unit_tail_only_unused_ring_removed_v1','module':target,'source_git_blob':source_blob,'source_sha256':source_sha,'source_bytes':len(source),'previous_source_git_blob':prior_source_blob,'previous_source_sha256':prior_source_sha,'exact_substitution':{'old':old_line.decode(),'new':new_line.decode(),'count':1},'all_statement_and_import_bytes_unchanged':True,'retained_strict_warningAsError':True,'original_guard_runner_validator_unchanged':tools_expected,'reuse_supply_receipt_sha256':sha(out/'SUPPLY_QUALIFICATION.json'),'no_supplier_source_kernel_owned_or_actual_import_probe_repeated':True,'borrowed_actual_parts_rehashed_unchanged':len(borrowed_imports['parts']),'failed_target_outputs_existed':False})


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

try:
 stable()
 normal_cmd=runprefix+['lake','env','lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(lib/(target.replace('.','/')+'.olean')),'-i',str(lib/(target.replace('.','/')+'.ilean')),str(src)]
 normal=stage('normal-build-unused-ring-fix',normal_cmd,allow_sources={str(src.resolve())},timeout=900)
 produced=source_outputs();save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',produced)
 after=actual_inputs('consumer-actual-imports',[target],produced)
 kernel=named_kernel('named-kernel',[target])
 owned,decls,inventory,axioms=full_owned('full-owned',[target])
 stage('runtime-final-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe','--require-source'])
 stable();assert source_outputs()==produced and sha(src)==source_sha
 save(out/'SOURCE_AND_OUTPUTS_AFTER.json',produced)
 all_commands=[json.loads(l)for l in guardlog.read_text().splitlines()if l]
 lean_sources=[str(P(r['cwd'])/a)if not P(a).is_absolute()else a for r in all_commands if r.get('tool')=='lean' for a in r.get('input_args',[])if a.endswith('.lean')]
 assert lean_sources==[str(src),str(src)],lean_sources
 result={'schema':'p29_unit_tail_count_P3_normal_named_kernel_full_owned_v1','result':'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED','module':target,'source_git_blob':source_blob,'source_sha256':source_sha,'source_bytes':len(source),'normal':normal,'kernel':kernel,'owned':owned,'owned_count':len(decls),'inventory':inventory,'observed_axioms':axioms,'all_owned_private_generated_types_and_universes':True,'actual_input_modules':after['module_count'],'actual_input_parts':after['part_count'],'actual_input_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'original_guard_runner_validator_unchanged':tools_expected,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'normal_source_invocations':lean_sources,'successful_normal_source_invocations':1,'failed_normal_source_invocations':1,'first_failed_normal_source_git_blob':prior_source_blob,'source_repair_record_sha256':sha(out/'SOURCE_REPAIR_AND_INPUT.json'),'borrowed_source_recompilations':0,'borrowed_module_count':18,'current_supply_receipt_sha256':sha(out/'SUPPLY_QUALIFICATION.json'),'direct_Lean_outputs':['.olean','.ilean'],'no_Lake_trace_or_setup_created':True,'full_P2_9_complete':False,'whole_standard_import_kernel_replay_claim':False,'scope':'The original scale-admitted unit-tail count and fixed-rank/all-rank power-error payment. Same literal log(N)/N normalizer; no additional source condition, additive-prime test, signed PP input, or full P2.9 closure.'}
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','module','owned_count','observed_axioms','actual_input_modules','actual_input_parts']}),flush=True)
except Exception as e:
 failure={'schema':'p29_unit_tail_count_P3_unused_ring_resume_failure_v1','root':str(root),'evidence':str(out),'error':str(e),'traceback':traceback.format_exc(),'completed_resume_stages':[r['stage']for r in runs],'reused_supply_receipt_sha256':sha(out/'SUPPLY_QUALIFICATION.json'),'changed_protected_parts':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s]}
 save(out/'FAILURE_unused_ring_resume.json',failure);print(json.dumps(failure),flush=True);raise

members={}
for p in out.rglob('*'):
 if p.is_file():members['verification/'+str(p.relative_to(out))]=p
for p in root.rglob('*'):
 if p.is_file()and (root/'.lake/packages')not in p.parents:members['project/'+str(p.relative_to(root))]=p
for p in (base/'original-tools').iterdir():members['original-tools/'+p.name]=p
for p in (base/'supplier-production').rglob('*'):
 if p.is_file():members['supplier-production/'+str(p.relative_to(base/'supplier-production'))]=p
members['SUPPLY_PREFLIGHT.json']=preflight
manifest={k:{'bytes':p.stat().st_size,'sha256':sha(p)}for k,p in members.items()}
save(base/'FILE_MANIFEST.json',{'schema':'p29_unit_tail_complete_current_receiver_evidence_v1','files':manifest,'excludes':['FILE_MANIFEST.json'],'borrowed_historical_archives_referenced_by_exact_Git_blob_and_sha256':True})
members['FILE_MANIFEST.json']=base/'FILE_MANIFEST.json'
archive=base/'qualified-unit-tail-count.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6)as t:
 for name,p in sorted(members.items()):t.add(p,arcname=name,recursive=False)
meta={'path':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),'members':len(members),'manifest_sha256':sha(base/'FILE_MANIFEST.json')}
save(base/'ARCHIVE_TRANSPORT.json',meta);print('P29_ARCHIVE '+json.dumps(meta),flush=True)
