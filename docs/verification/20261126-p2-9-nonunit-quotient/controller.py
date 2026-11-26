import os,sys,pathlib,json,hashlib,subprocess,signal,time,datetime,re,importlib.util,traceback,tomllib,tarfile,ast,shutil,difflib,base64
P=pathlib.Path
def sha(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()

def stamp(p):
 s=P(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

def save(p,x):
 p=P(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(x,f,indent=2);f.write('\n')

def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()

def register_part(path,identity,snapshot,authority):
 path=str(path);p=P(path);st=stamp(p)
 if st!=snapshot:assert sha(p)==identity['sha256'],('Accepted import drift',path)
 cache_before[path]=st
 row={'identity':{'path':path,'bytes':identity['bytes'],'sha256':identity['sha256']},'stat_snapshot':st,'authority':authority}
 for key in [path,str(p.resolve())]:
  if key in knownparts:assert knownparts[key]['identity']['sha256']==identity['sha256'],('Accepted aliases disagree',key)
  knownparts[key]=row

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

def bind_release():
 rec=stage('pinned-lean-version',runprefix+['lake','env','lean','--version'])
 ver=(out/'pinned-lean-version.log').read_text().strip()
 assert 'version 4.33.0-rc1,'in ver and 'commit '+LEAN_COMMIT+','in ver,ver
 stage('pinned-lean-prefix',runprefix+['lake','env','lean','--print-prefix'])
 prefix=(out/'pinned-lean-prefix.log').read_text().splitlines()
 shadow=P(state['shadow'])
 assert prefix and P(prefix[-1])==shadow and state['environment']['LEAN_SYSROOT']==str(shadow),('Guard-reported shadow prefix mismatch',prefix,shadow)
 assert P(state['realbin'])==(TC/'bin').resolve() and (shadow/'lib').is_symlink() and (shadow/'lib/lean').resolve()==TOOL_LIB,('Wrong actual guarded library carrier',shadow,TC)
 release_binding['guarded_shadow']={'prefix':str(shadow),'release_lib_from_shadow':str((shadow/'lib/lean').resolve()),'state_sha256':state_sha_before}
 for name,shadow_name in [('lean','lean-runtime'),('lake','lake')]:
  p=TC/'bin'/name;q=shadow/'bin'/shadow_name
  assert p.is_file()and q.is_file()and not q.is_symlink()
  digest=sha(p);assert digest==sha(q)==state['runtime_sha256'][str(p)]==state['runtime_sha256'][str(q)],('Pinned guard binary copies differ',p,q)
  entry={'path':str(p),'bytes':p.stat().st_size,'sha256':digest,'shadow_binary':str(q)}
  cache_before[str(p)]=stamp(p);cache_before[str(q)]=stamp(q);release_binding[name]=entry
 release_binding.update(pin=PIN,lean_commit=LEAN_COMMIT,sysroot=str(TC),lib_root=str(TOOL_LIB),
   version_log_sha256=rec['log_sha256'],workspace_toolchain_sha256=sha(root/'lean-toolchain'))
 save(out/'PINNED_TOOLCHAIN.json',release_binding)

INPUTS=[{'module': 'ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient', 'blob': '0117dd4f635e04bed4a5191f06295a442975a0b4', 'bytes': 3380, 'sha256': '6b11d4a2bc7838dbdda9e1354b796f659d7782dbd3d62fcec372f49f898611ef', 'source': "import ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass\nimport MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform\n\n/-!\nAt the actual frozen Gamma5 cutoff, the nonunit rough count has a\nuniform upper bound for every real height up to N. For a partial prime\ntuple of product D ≥ 2 its remaining height 2N/D is in that range.\nThe imported uniform estimate supplies both sides of the transition.\n-/\nnamespace ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient\n\nnoncomputable section\nopen Filter Real LiLiuPrereqBuchstab\nopen P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent cutExponent_pos norm)\nopen scoped Topology\n\n/-- One target threshold precedes the real height. The unit is excluded\nalso when the height is below the actual cutoff. -/\ntheorem eventually_nonunit_card_le :\n    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 ≤ x → x ≤ (N : ℝ) →\n      (((roughNumbers x (cut N)).erase 1).card : ℝ) ≤\n        (2 / cutExponent) * (x / log (N : ℝ)) := by\n  obtain ⟨T, hT4, H⟩ := Wu2008DoubleSieve.NonunitRoughUniform.uniform_upper\n    cutExponent_pos (zero_lt_one : (0 : ℝ) < 1)\n  filter_upwards [eventually_ge_atTop T] with N hN\n  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)\n  have hN0 := zero_lt_one.trans hNr\n  have hlog := log_pos hNr\n  have hcut : 1 < cut N := one_lt_rpow hNr cutExponent_pos\n  have hL : log (cut N) = cutExponent * log (N : ℝ) := log_rpow hN0 _\n  intro x hx hxN\n  obtain ⟨hempty, hcount⟩ := H N hN x (cut N) hxN (le_refl _)\n  by_cases hy : cut N ≤ x\n  · have hu := Wu2008DoubleSieve.NonunitRoughUniform.log_ratio_ge_one hcut hy\n    have hb : buchstab (log x / log (cut N)) + 1 ≤ 2 := by\n      linarith only [buchstab_le_one hu]\n    calc\n      _ ≤ _ := hcount hy\n      _ ≤ 2 * x / log (cut N) :=\n        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hx) (log_pos hcut).le\n      _ = _ := by\n        rw [hL]\n        field_simp [cutExponent_pos.ne', hlog.ne'] <;> ring\n  · rw [hempty (lt_of_not_ge hy), Nat.cast_zero]\n    exact mul_nonneg (div_nonneg (by norm_num) cutExponent_pos.le) (div_nonneg hx hlog.le)\n\n/-- The original log N / N normalization gives an inverse-product\nweight, with a constant fixed before N or the partial product D. -/\ntheorem eventually_nonunit_quotient_le :\n    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, 2 ≤ D →\n      norm N * (((roughNumbers (2 * (N : ℝ) / (D : ℝ)) (cut N)).erase 1).card : ℝ) ≤\n        (4 / cutExponent) / (D : ℝ) := by\n  filter_upwards [eventually_nonunit_card_le, eventually_gt_atTop (1 : ℕ)]\n    with N H hN\n  intro D hD\n  have hNr : (1 : ℝ) < N := by exact_mod_cast hN\n  have hN0 := zero_lt_one.trans hNr\n  have hlog := log_pos hNr\n  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD\n  have hD0 : (0 : ℝ) < D := by linarith only [hDr]\n  have hcap : 2 * (N : ℝ) / (D : ℝ) ≤ (N : ℝ) := by\n    apply (div_le_iff₀ hD0).mpr\n    calc\n      _ ≤ (D : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right hDr hN0.le\n      _ = _ := mul_comm _ _\n  have hu := H (2 * (N : ℝ) / (D : ℝ))\n    (div_nonneg (mul_nonneg (by norm_num) hN0.le) hD0.le) hcap\n  have hn : 0 ≤ norm N := div_nonneg hlog.le hN0.le\n  calc\n    _ ≤ _ := mul_le_mul_of_nonneg_left hu hn\n    _ = _ := by\n      unfold norm\n      field_simp [hN0.ne', hlog.ne', hD0.ne', cutExponent_pos.ne'] <;> ring\n\nend\nend ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient\n"}]
IMMUTABLE_PINS={'/workspace/p29-radial-profile-verification-20261125-pinbind-v4/VALIDATION_RESULTS.json': '5742156c6b46da61149f1355c0bbe33b22cb54d803ad33b4346c1c9d6c42051f', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/SOURCE_AND_OUTPUTS_AFTER.json': '9a38a315c2bbac38f5a85ea10b0051c80358bd08fe2a66128bf4d1e0d848f0a4', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/consumer-actual-imports-bindings.json': 'f99a3aea2dc3b103e793dfe1f96cc7cbac0897ba3ec053b077bdbb7021e78de8', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/BORROWED_OBJECTS.json': '01f254264580b22f22c2e20caaba30b13d309656099d7127f49e2d6cb5022562', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/P2_CURRENT_P1_QUALIFICATION.json': 'e4eded9de6f8f361de93da40e9615eb0e75e7ce05e110561ca08ea4b7151bc19', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/P1_FIVE_IMPORT_COMPARISON.json': 'c28904e9a8c3dd671128810c1dd513bdd61ae6197944691b573652db6a65fbb1', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/PP_MAX_STEPS_RESOLUTION.json': '9784a1c67167e9d67861d0fde85b9d8a5a0eb2df496ea0d81d374bb4b6dbaabb', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/driver.py': 'ceb4f796dc7a362e47ae49fb0a2300f425c769500610e7c8baa09a6580b2170e', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/driver-pp1e6-resume.py': 'fad03cf7d93979bdaab9dfb681089ea1bc581a31860b0f469b0c59bcb140964a', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-evidence/state.json': '93dd7569b9434e6c5bc4a795fb194f7050dc8f9eee8eaf8fea15df56b3fe0bec', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-evidence/audit.json': '9bd091734012e9e8c38b1d4c5d792ec5a55f2ea18aee3ca40a368afd059c77d1', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-evidence/compiler-commands.jsonl': '67e08b94cda9b21cb7ee91ac58ee591f5f7619dd4e9fe8cbff5cf2d3f6861b42', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/FAILURE.json': 'ec27af46c62c1b54f95d1da40fc797944ebeb64b2972ad8aae692bcf5870e22e', '/workspace/p29-radial-profile-20261125-pinbind-v4/lakefile.toml': '70ab0b7423ca1c3cbf690573ecaf580e2290ff9ad5c59015b556e068d415e2ff', '/workspace/p29-radial-profile-20261125-pinbind-v4/lake-manifest.json': '0c1ed2f4476d4b54d5376b98606e861fd7ecc822ddf3977831f48469c83fc54b', '/workspace/p29-radial-profile-20261125-pinbind-v4/lean-toolchain': '62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef', '/workspace/p29-nonunit-supply-20261125-0238173d/BINDING_RECEIPT.json': 'c70b4abe99b6335384c42c05e241611979a6da1119cf1e4883ee87dee42b3788', '/workspace/p29-nonunit-supply-20261125-0238173d/VALIDATION_RESULTS.json': '9664afeec28214c01e08d54c36a8effc1259f5beb50e2c00389c58f1b490da29', '/workspace/p29-nonunit-supply-20261125-0238173d/SOURCE_AND_OUTPUTS_AFTER.json': '94dfaa2d15bb5d4c7687b1289636b207175676f9173a4e41e4759b57616c39bc', '/workspace/p29-nonunit-supply-20261125-0238173d/controller-evidence/ACTUAL_IMPORT_PART_BINDINGS.json': 'c031a7e3c5773ecdf934bb8d286adbba917162bde305ede2b2fd0061765484d6', '/workspace/p29-nonunit-supply-20261125-0238173d/controller-evidence/PRODUCER_BINDINGS.json': '8009323d35bc0d3efd12b3199ba11b8aca608ef1081e4df71d5286f5e6f01277'}

priorroot=P('/workspace/p29-radial-profile-20261125-pinbind-v4')
priorout=P('/workspace/p29-radial-profile-verification-20261125-pinbind-v4')
nativeout=P('/workspace/p29-nonunit-supply-20261125-0238173d')
root=P('/workspace/p29-nonunit-quotient-20261126-0117dd4')
out=P('/workspace/p29-nonunit-quotient-verification-20261126-0117dd4')
assert not root.exists()and not out.exists(),'Do not repeat a submitted target continuation.'
GUARD=P('/workspace/goldbach-formalization/docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/ci_runtime_guard.py')
RUNNER=P('/workspace/blue-build-tools/run_guarded.py')
OWNED=P('/workspace/blue-build-tools/validate_member_roots_owned.py')
tools_expected={str(GUARD):'837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877',str(RUNNER):'c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526',str(OWNED):'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'}
assert all(sha(p)==h for p,h in tools_expected.items())
assert all(sha(p)==h for p,h in IMMUTABLE_PINS.items())
prior_pin_stamps={p:stamp(p)for p in IMMUTABLE_PINS}
original_tree=ast.parse((priorout/'driver.py').read_text())
original_literals={n.targets[0].id:ast.literal_eval(n.value)for n in original_tree.body if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)and isinstance(n.value,ast.Constant)}
AUDIT_TEMPLATE=json.loads(original_literals['AUDIT_TEXT'])
PIN='leanprover/lean4:v4.33.0-rc1'
LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux').resolve()
TOOL_LIB=(TC/'lib/lean').resolve()
package_revisions={'mathlib':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','plausible':'b1c4a69a7e247ab7df20460212001673d74f08c0','LeanSearchClient':'0498c7c070c143a3bf7379f4d99a2c63bb9d9715','importGraph':'18a90119a5d316358fde6c86e0ca24e59212e32c','proofwidgets':'b1436dc749e722c9920036b52cdc43b3451d0b69','aesop':'57d3325be72a842920813bcb40f96a6f7393c185','Qq':'ee41917ae11d38479fb8fb24745f7ca4bf0a784d','batteries':'41bd267b3f6b7252f6676af46d4ffc6783b64de9','Cli':'da07ca808b6718cb2aed14dba154e5a08b8f8ecf'}
package_bindings={};release_binding={}
mods=[x['module']for x in INPUTS]
assert mods==['ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient']
direct_imports=['ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass','MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform']
project_suppliers=['ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants','ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass']
native_modules=['MathlibNt.Wu2008DoubleSieve.NonunitRoughUniformCore','MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform']
for row in INPUTS:
 b=row['source'].encode();assert len(b)==row['bytes']and hashlib.sha256(b).hexdigest()==row['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['blob']
 assert re.findall(r'(?m)^import ([A-Za-z0-9_.]+)$',row['source'])==direct_imports
prior_result=json.loads((priorout/'VALIDATION_RESULTS.json').read_text())
assert prior_result['result']=='PASS_TWO_NEW_CONSUMERS_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED'
assert prior_result['owned_declarations']==21 and prior_result['recompiled_old_project_or_native_sources']==0
old_borrows=json.loads((priorout/'BORROWED_OBJECTS.json').read_text())['objects']
old_state=json.loads((priorout/'runtime-evidence/state.json').read_text())
accepted_policy=old_state['policy']
native_receipt=json.loads((nativeout/'BINDING_RECEIPT.json').read_text())
native_validation=json.loads((nativeout/'VALIDATION_RESULTS.json').read_text())
native_outputs=json.loads((nativeout/'SOURCE_AND_OUTPUTS_AFTER.json').read_text())
assert native_receipt['status']=='PASS_CURRENT_P1_EXISTING_NONUNIT_SUPPLY'and native_receipt['modules']==native_modules
assert native_receipt['source_recompilations']==0 and native_receipt['owned_declaration_counts']==dict(zip(native_modules,[19,11]))
assert native_validation['result']=='PASS_EXACT_MODULE_REPLAY_FULL_OWNED_DECLARATION_TYPES_AND_STANDARD_AXIOMS'
assert native_validation['modules']==native_modules and native_validation['kernel']['exit_code']==native_validation['types_and_axioms']['exit_code']==0
assert native_validation['source_and_five_outputs_per_module']==native_outputs
root.mkdir();out.mkdir();(out/'driver.py').write_text(SOURCE_TEXT)
save(out/'INPUTS.json',[{k:v for k,v in row.items()if k!='source'}for row in INPUTS])
save(out/'PRIOR_EVIDENCE_PINS.json',{'pins':IMMUTABLE_PINS,'stat_snapshots':prior_pin_stamps,'original_P1_root':str(priorroot),'original_P1_evidence':str(priorout),'native_nonunit_evidence':str(nativeout),'P1_root_acceptance_commit_prefix':'f0c76b36','native_receipt_git_blob':'724a1f6ff7a3063fa8fe76905667b042340e57d0','native_validation_git_blob':'a8c0d096018457b40fa182b1c25e860088b233a5','native_outputs_git_blob':'3cf2f51469aecab16dfe07b794e6d0b17f70dc99','old_source_compilations':0,'old_kernel_replays':0,'old_owned_replays':0,'old_nonunit_type_representation':native_receipt['type_representation']})
for oldname,newname in [('runtime-evidence/compiler-commands.jsonl','ORIGINAL_P1_GUARD_LOG.jsonl'),('runtime-evidence/audit.json','ORIGINAL_P1_RUNTIME_AUDIT.json'),('runtime-evidence/state.json','ORIGINAL_P1_RUNTIME_STATE.json'),('VALIDATION_RESULTS.json','ORIGINAL_P1_VALIDATION_RESULTS.json'),('FAILURE.json','ORIGINAL_P1_FAILURE.json')]:
 shutil.copyfile(priorout/oldname,out/newname)
for name in ['BINDING_RECEIPT.json','VALIDATION_RESULTS.json','SOURCE_AND_OUTPUTS_AFTER.json']:
 shutil.copyfile(nativeout/name,out/('ORIGINAL_NONUNIT_'+name))
cache_before={};protected_outputs={};knownparts={};borrows={};expected_hashes={};expected_authorities={}

def accept_part(module,identity,historical_stat,authority):
 path=identity['path'];p=P(path);current=stamp(p)
 assert current[2]==identity['bytes']and sha(p)==identity['sha256'],('Accepted facet bytes changed',module,path)
 facet=facet_of(module,path)
 assert facet in {'.olean','.olean.server','.olean.private','.ir.sig','.ir'},('Unexpected accepted facet',module,path)
 key=(module,facet)
 if key in expected_hashes:assert expected_hashes[key]==identity['sha256'],('Prior suppliers disagree on module/facet',module,facet)
 expected_hashes[key]=identity['sha256'];expected_authorities.setdefault(key,[]).append({'authority':authority,'path':path,'original_stat_snapshot':historical_stat})
 register_part(path,identity,current,authority)

p1_graph=json.loads((priorout/'consumer-actual-imports-bindings.json').read_text())
assert p1_graph['module_count']==6199 and p1_graph['part_count']==30835
assert len(p1_graph['parts'])==30835
for part in p1_graph['parts']:
 assert part['facet']==facet_of(part['module'],part['identity']['path'])
 accept_part(part['module'],part['identity'],part['stat_snapshot'],'accepted_P1_profile_actual_part')
 if part['requested_path']in knownparts:assert knownparts[part['requested_path']]['identity']['sha256']==part['identity']['sha256']
 else:knownparts[part['requested_path']]=knownparts[part['identity']['path']]
native_graph=json.loads((nativeout/'controller-evidence/ACTUAL_IMPORT_PART_BINDINGS.json').read_text())
assert native_graph['schema']=='p29_nonunit_current_resolved_setup_parts_v1'and native_graph['missing_parts']==[]
assert len(native_graph['parts'])==19197 and len({p['module']for p in native_graph['parts']})==3857
assert native_graph['counts']=={'accepted_twelve_native_actual_import_memo':19184,'accepted_twelve_native_produced_output':12,'this_exact_core_object_with_current_producer_binding':1}
for part in native_graph['parts']:accept_part(part['module'],part['identity'],part['current_stat_snapshot'],'accepted_nonunit_current_setup_part')
for source_doc in [json.loads((priorout/'SOURCE_AND_OUTPUTS_AFTER.json').read_text()),native_outputs]:
 for path,identity in source_doc.items():
  assert P(path).stat().st_size==identity['bytes']and sha(path)==identity['sha256']
  protected_outputs[path]=identity;cache_before[path]=stamp(path)
producer=json.loads((nativeout/'controller-evidence/PRODUCER_BINDINGS.json').read_text())
assert producer['schema']=='p29_nonunit_exact_current_producer_binding_v1'and producer['blockers']==[]
assert [p['module']for p in producer['modules']]==native_modules
for row in producer['modules']:
 module=row['module'];identity=row['olean'];path=identity['path']
 assert path.endswith('/'+module.replace('.','/')+'.olean')
 assert {k:identity[k]for k in ['bytes','sha256']}==native_outputs[path]
 for item in [row['source'],row['olean'],row['trace'],row['setup'],*row['sidecars']]:
  p=item['path'];assert P(p).stat().st_size==item['bytes']and sha(p)==item['sha256'];cache_before[p]=stamp(p)
 accept_part(module,identity,stamp(path),'accepted_nonunit_own_output_from_exact_producer')
lib=root/'.lake/build/lib/lean'
for module in project_suppliers:
 prior=old_borrows[module];original=P(prior['object']);source_path=P(prior['source'])
 assert sha(original)==prior['object_sha256']and original.stat().st_size==prior['object_bytes']and sha(source_path)==prior['source_sha256']
 assert expected_hashes[(module,'.olean')]==prior['object_sha256']
 dest=lib/(module.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(original,dest)
 assert sha(dest)==prior['object_sha256'];cache_before[str(dest)]=stamp(dest);cache_before[str(original)]=stamp(original);cache_before[str(source_path)]=stamp(source_path)
 protected_outputs[str(original)]={'bytes':original.stat().st_size,'sha256':prior['object_sha256']};protected_outputs[str(source_path)]={'bytes':source_path.stat().st_size,'sha256':prior['source_sha256']}
 borrows[module]={'module':module,'origin':'accepted_P1_radial_exact_olean_copy','source':str(source_path),'source_sha256':prior['source_sha256'],'object':str(dest),'object_sha256':prior['object_sha256'],'object_bytes':prior['object_bytes'],'original_object':str(original),'original_record':prior,'original_facets_copied':['.olean'],'other_facets_created':False}
save(out/'BORROWED_OBJECTS.json',{'module_count':len(borrows),'objects':borrows,'native_modules_reused_in_existing_package':native_modules,'new_supplier_credit':0})
old_toml=(priorroot/'lakefile.toml').read_text();old_config=tomllib.loads(old_toml)
old_scope=old_config['lean_lib'][0]
assert old_scope['name']=='ImbalancedChen'and old_scope['roots']==old_scope['globs']==prior_result['modules']
new_toml=old_toml
for key in ['roots','globs']:
 before_line=key+' = '+json.dumps(old_scope[key])+'\n';after_line=key+' = '+json.dumps(mods)+'\n'
 assert new_toml.count(before_line)==1;new_toml=new_toml.replace(before_line,after_line,1)
new_config=tomllib.loads(new_toml);compared=json.loads(json.dumps(new_config))
compared['lean_lib'][0]['roots']=old_scope['roots'];compared['lean_lib'][0]['globs']=old_scope['globs']
assert compared==old_config and new_config['moreLeanArgs']==['-DmaxRecDepth=100000','-DmaxHeartbeats=4000000']
assert 'warningAsError'not in new_toml
(root/'lakefile.toml').write_text(new_toml);(out/'ORIGINAL_P1_LAKEFILE.toml').write_text(old_toml)
(out/'LAKEFILE_EXACT_DIFF.patch').write_text(''.join(difflib.unified_diff(old_toml.splitlines(True),new_toml.splitlines(True),fromfile=str(priorroot/'lakefile.toml'),tofile=str(root/'lakefile.toml'))))
for name in ['lake-manifest.json','lean-toolchain']:shutil.copyfile(priorroot/name,root/name)
assert(root/'lean-toolchain').read_text().strip()==PIN
config_before={str(root/name):sha(root/name)for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
save(out/'CONFIGURATION_ADAPTATION.json',{'original_root':str(priorroot),'new_root':str(root),'original_lakefile_sha256':sha(priorroot/'lakefile.toml'),'new_lakefile_sha256':sha(root/'lakefile.toml'),'changes_only':{'lean_lib.roots':mods,'lean_lib.globs':mods},'all_other_bytes_unchanged':True,'normal_warning_as_error_requested':False,'old_root_and_runtime_unchanged':True})
allowed_sources=set()
for row in INPUTS:
 p=root/(row['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(row['source'].encode());allowed_sources.add(str(p.resolve()))
 rel=row['module'].replace('.','/')
 assert all(not q.exists()for q in [lib/(rel+s)for s in ['.olean','.ilean','.trace']]+[root/'.lake/build/ir'/(rel+s)for s in ['.c','.setup.json']])
runtime_parent=root/'runtime';runtime_parent.mkdir();runtime_evidence=out/'runtime-evidence'
base_env=os.environ.copy()
for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR='/workspace/blue-build-tools/lean-action',GITHUB_ENV=str(out/'runtime.env'),GITHUB_PATH=str(out/'runtime.path'))
base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
setup_cmd=['python3',str(GUARD),'setup','--evidence',str(runtime_evidence)]
with(out/'runtime-setup.log').open('xb')as f:r=subprocess.run(setup_cmd,cwd=root,env=base_env,stdout=f,stderr=subprocess.STDOUT)
save(out/'runtime-setup-process.json',{'command':setup_cmd,'cwd':str(root),'exit_code':r.returncode,'log_sha256':sha(out/'runtime-setup.log')})
assert r.returncode==0,'Original runtime guard setup failed'
state_path=runtime_evidence/'state.json';state=json.loads(state_path.read_text());guardlog=P(state['log']);state_sha_before=sha(state_path)
assert state['policy']==accepted_policy and state['input_sha256']==config_before
runprefix=['python3',str(RUNNER),'--state',str(state_path)];runs=[]
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED);auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)

def exact_merged_inputs(data,hashes,production=None):
 production=production or {};allowed=dict(expected_hashes)
 for path,identity in production.items():
  for module in mods:
   if str(path).endswith('/'+module.replace('.','/')+'.olean'):allowed[(module,'.olean')]=identity['sha256']
 assert all(key in allowed and value==allowed[key]for key,value in hashes.items()),'Actual merged graph contains an unqualified module/facet or changed bytes'
 assert all(not row['authority'].startswith('fresh_')for row in data['parts']),'Fresh external authority is not accepted in this continuation'
 assert set(hashes)>={(m,'.olean')for m in direct_imports}
 return {'module_count':data['module_count'],'part_count':data['part_count'],'every_actual_part_matches_exact_prior_authority_or_target_output':True,'new_external_authorities':0,'old_source_compilations':0,'old_kernel_replays':0,'old_owned_replays':0}

try:
 stage('runtime-initial-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe'])
 bind_release()
 before,actual_before,hashes_before=load_actual_imports('merged-supplier-actual-imports',direct_imports)
 before_check=exact_merged_inputs(before,hashes_before)
 assert all(sha(p)==h and stamp(p)==prior_pin_stamps[p]for p,h in IMMUTABLE_PINS.items())
 save(out/'EXACT_SUPPLIER_REUSE.json',{'schema':'p29_nonunit_quotient_exact_prior_union_reuse_v1','status':'PASS_EXACT_MERGED_INPUTS_WITHOUT_SUPPLIER_REPLAY','before':before_check,'actual_bindings_sha256':sha(out/'merged-supplier-actual-imports-bindings.json'),'P1_actual_bindings_sha256':sha(priorout/'consumer-actual-imports-bindings.json'),'native_actual_bindings_sha256':sha(nativeout/'controller-evidence/ACTUAL_IMPORT_PART_BINDINGS.json'),'native_producer_bindings_sha256':sha(nativeout/'controller-evidence/PRODUCER_BINDINGS.json'),'native_receipt_sha256':sha(nativeout/'BINDING_RECEIPT.json'),'native_type_representation':native_receipt['type_representation'],'native_Core_19_Upper_11_reused_no_new_credit':True,'old_mathematical_credit_added':0})
 normal=stage('normal-build',runprefix+['lake','build',*['+'+m+':olean'for m in mods]],allow_sources=allowed_sources)
 production=source_outputs();save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',production)
 after,actual_after,hashes_after=load_actual_imports('consumer-actual-imports',mods,production)
 after_check=exact_merged_inputs(after,hashes_after,production)
 assert {k:v for k,v in hashes_after.items()if k[0]not in mods}==hashes_before,'Target changed the exact imported closure'
 setup_matches=[]
 for module in mods:
  path=root/'.lake/build/ir'/(module.replace('.','/')+'.setup.json');setup=json.loads(path.read_text());assert setup['name']==module
  assert not setup.get('options',{}).get('warningAsError',False)
  checked=0
  for dep,groups in setup['importArts'].items():
   for group in groups:
    for p in group:
     assert hashes_after.get((dep,facet_of(dep,p)))==sha(p),('Lake actual importArts differs from actual loader',module,dep,p)
     checked+=1
  setup_matches.append({'module':module,'setup_path':str(path),'setup_sha256':sha(path),'explicit_setup_artifact_count':checked,'explicit_parts_match_current_resolver':True})
 save(out/'CONSUMER_SETUP_IMPORT_MATCH.json',setup_matches)
 kernel=named_kernel('named-kernel',mods)
 owned,decls,inventory,axioms=full_owned('full-owned',mods)
 assert {mods[0]+'.eventually_nonunit_card_le',mods[0]+'.eventually_nonunit_quotient_le'}<={r['name']for r in decls}
 stock=stage('final-stock',runprefix+['lake','--no-build','build',*['+'+m+':olean'for m in mods]])
 assert not any(r.get('tool')=='lean'and('--stdin'in r.get('input_args',[])or any(str(a).endswith('.lean')for a in r.get('input_args',[])))for r in stock['guarded_commands'])
 stage('runtime-final-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe','--require-source'])
 final=source_outputs();assert final==production
 assert sha(state_path)==state_sha_before and {p:sha(p)for p in config_before}==config_before
 assert all(sha(p)==h for p,h in tools_expected.items())
 assert all(sha(p)==h and stamp(p)==prior_pin_stamps[p]for p,h in IMMUTABLE_PINS.items())
 assert all(sha(p)==r['sha256']for p,r in protected_outputs.items())
 changed=[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s];assert not changed,('Accepted or produced parts changed',changed[:20])
 all_commands=[json.loads(l)for l in guardlog.read_text().splitlines()if l]
 source_calls=[str((P(r['cwd'])/a).resolve())if not P(a).is_absolute()else str(P(a).resolve())for r in all_commands if r.get('tool')=='lean'for a in r.get('input_args',[])if str(a).endswith('.lean')]
 assert len(source_calls)==1 and set(source_calls)==allowed_sources,source_calls
 normal_warnings=[line for line in(out/'normal-build.log').read_text().splitlines()if line.startswith('warning:')]
 save(out/'SOURCE_AND_OUTPUTS_AFTER.json',final)
 result={'schema':'p29_nonunit_quotient_original_source_normal_kernel_full_owned_v1','result':'PASS_ONE_NEW_NONUNIT_QUOTIENT_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED','root':str(root),'evidence':str(out),'modules':mods,'inputs':[{k:v for k,v in row.items()if k!='source'}for row in INPUTS],'normal':normal,'normal_warning_as_error_requested':False,'normal_warning_count':len(normal_warnings),'normal_warnings':normal_warnings,'kernel':kernel,'owned':owned,'stock':stock,'owned_declarations':len(decls),'owned_declaration_counts':inventory['module_counts'],'observed_axioms':axioms,'full_owned_private_generated_ast_universes':True,'actual_import_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'before_actual_import_bindings_sha256':sha(out/'merged-supplier-actual-imports-bindings.json'),'exact_supplier_reuse_receipt_sha256':sha(out/'EXACT_SUPPLIER_REUSE.json'),'consumer_setup_import_match_sha256':sha(out/'CONSUMER_SETUP_IMPORT_MATCH.json'),'normal_source_invocations':source_calls,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'prior_evidence_and_old_runtime_unchanged':True,'old_source_recompilations':0,'old_kernel_replays':0,'old_owned_replays':0,'old_supplier_new_formal_credit':0,'native_supplier_type_representation':native_receipt['type_representation'],'new_actual_external_authorities':0,'runtime_policy':state['policy'],'original_audited_tools_unchanged':tools_expected,'scope_note':'Existing frozen Gamma5 nonunit real-height count and inverse-product quotient bound only. No new manuscript-external statement, aggregate wall payment, signed PP estimate, or full P2.9 conclusion is claimed.'}
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','root','evidence','modules','owned_declarations','owned_declaration_counts','observed_axioms','normal_warning_as_error_requested','normal_warning_count','monitored_parts_unchanged']}),flush=True)
 print(json.dumps({'validation_results_sha256':sha(out/'VALIDATION_RESULTS.json'),'source_outputs_sha256':sha(out/'SOURCE_AND_OUTPUTS_AFTER.json'),'declarations_sha256':sha(out/'full-owned-DECLARATION_TYPES_AXIOMS.json'),'inventory_sha256':sha(out/'full-owned-INVENTORY_NAME_SET_CHECK.json')}),flush=True)
except Exception as e:
 failure={'schema':'p29_nonunit_quotient_continuation_failure_v1','root':str(root),'evidence':str(out),'error':str(e),'traceback':traceback.format_exc(),'completed_stages':[r['stage']for r in runs],'old_evidence_changed':[p for p,h in IMMUTABLE_PINS.items()if not P(p).is_file()or sha(p)!=h],'borrowed_cache_changed':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s]}
 save(out/'FAILURE.json',failure);print(json.dumps(failure),flush=True);raise

export=out/'portable';export.mkdir()
entries={'evidence/'+str(p.relative_to(out)):p for p in out.rglob('*')if p.is_file()and export not in p.parents}
entries.update({'config/'+name:root/name for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']})
for path in final:
 p=P(path);entries['project/'+str(p.relative_to(root))]=p
inventory={name:{'bytes':p.stat().st_size,'sha256':sha(p)}for name,p in entries.items()}
save(export/'COMPLETE_MEMBERS.json',inventory);entries['COMPLETE_MEMBERS.json']=export/'COMPLETE_MEMBERS.json'
archive=export/'NONUNIT_QUOTIENT_COMPLETE_EVIDENCE.tar.xz'
with tarfile.open(archive,'w:xz',preset=9)as tar:
 for name,path in sorted(entries.items()):tar.add(path,arcname=name,recursive=False)
emit=archive.stat().st_size<=5600000
print('P29_ARCHIVE '+json.dumps({'name':archive.name,'path':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),'files':len(entries),'emitted':emit,'compression':'xz preset9'}),flush=True)
if emit:print('P29_DATA '+archive.name+' '+base64.b64encode(archive.read_bytes()).decode(),flush=True)
