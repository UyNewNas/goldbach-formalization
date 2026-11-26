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

def accept_part(module,identity,historical_stat,authority):
 path=identity['path'];p=P(path);current=stamp(p)
 assert current[2]==identity['bytes']and sha(p)==identity['sha256'],('Accepted facet bytes changed',module,path)
 facet=facet_of(module,path)
 assert facet in {'.olean','.olean.server','.olean.private','.ir.sig','.ir'},('Unexpected accepted facet',module,path)
 key=(module,facet)
 if key in expected_hashes:assert expected_hashes[key]==identity['sha256'],('Prior suppliers disagree on module/facet',module,facet)
 expected_hashes[key]=identity['sha256'];expected_authorities.setdefault(key,[]).append({'authority':authority,'path':path,'original_stat_snapshot':historical_stat})
 register_part(path,identity,current,authority)

def exact_merged_inputs(data,hashes,production=None):
 production=production or {};allowed=dict(expected_hashes)
 for path,identity in production.items():
  for module in mods:
   if str(path).endswith('/'+module.replace('.','/')+'.olean'):allowed[(module,'.olean')]=identity['sha256']
 assert all(key in allowed and value==allowed[key]for key,value in hashes.items()),'Actual merged graph contains an unqualified module/facet or changed bytes'
 assert all(not row['authority'].startswith('fresh_')for row in data['parts']),'Fresh external authority is not accepted in this continuation'
 assert set(hashes)>={(m,'.olean')for m in direct_imports}
 return {'module_count':data['module_count'],'part_count':data['part_count'],'every_actual_part_matches_exact_prior_authority_or_target_output':True,'new_external_authorities':0,'old_source_compilations':0,'old_kernel_replays':0,'old_owned_replays':0}

INPUTS=[{'module': 'ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient', 'blob': 'eeaf7a2c714da44928cc43e79780846e1e72d23b', 'bytes': 3431, 'sha256': '42de161d084cac904775203fb0188bcc7bc5459a9b230b53c5c405e692262d77', 'source': "import ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass\nimport MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform\n\n/-!\nAt the actual frozen Gamma5 cutoff, the nonunit rough count has a\nuniform upper bound for every real height up to N. For a partial prime\ntuple of product D ≥ 2 its remaining height 2N/D is in that range.\nThe imported uniform estimate supplies both sides of the transition.\n-/\nnamespace ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient\n\nnoncomputable section\nopen Filter Real LiLiuPrereqBuchstab\nopen P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent cutExponent_pos norm)\nopen scoped Topology\n\n/-- One target threshold precedes the real height. The unit is excluded\nalso when the height is below the actual cutoff. -/\ntheorem eventually_nonunit_card_le :\n    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 ≤ x → x ≤ (N : ℝ) →\n      (((roughNumbers x (cut N)).erase 1).card : ℝ) ≤\n        (2 / cutExponent) * (x / log (N : ℝ)) := by\n  obtain ⟨T, hT4, H⟩ := Wu2008DoubleSieve.NonunitRoughUniform.uniform_upper\n    cutExponent_pos (zero_lt_one : (0 : ℝ) < 1)\n  filter_upwards [eventually_ge_atTop T] with N hN\n  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)\n  have hN0 := zero_lt_one.trans hNr\n  have hlog := log_pos hNr\n  have hcut : 1 < cut N := one_lt_rpow hNr cutExponent_pos\n  have hL : log (cut N) = cutExponent * log (N : ℝ) := log_rpow hN0 _\n  intro x hx hxN\n  obtain ⟨hempty, hcount⟩ := H N hN x (cut N) hxN (le_refl _)\n  by_cases hy : cut N ≤ x\n  · have hu := Wu2008DoubleSieve.NonunitRoughUniform.log_ratio_ge_one hcut hy\n    have hb : buchstab (log x / log (cut N)) + 1 ≤ 2 := by\n      linarith only [buchstab_le_one hu]\n    calc\n      _ ≤ _ := hcount hy\n      _ ≤ 2 * x / log (cut N) :=\n        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hx) (log_pos hcut).le\n      _ = _ := by\n        rw [hL]\n        field_simp [cutExponent_pos.ne', hlog.ne'] <;> ring\n  · rw [hempty (lt_of_not_ge hy), Nat.cast_zero]\n    exact mul_nonneg (div_nonneg (by norm_num) cutExponent_pos.le) (div_nonneg hx hlog.le)\n\n/-- The original log N / N normalization gives an inverse-product\nweight, with a constant fixed before N or the partial product D. -/\ntheorem eventually_nonunit_quotient_le :\n    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, 2 ≤ D →\n      norm N * (((roughNumbers (2 * (N : ℝ) / (D : ℝ)) (cut N)).erase 1).card : ℝ) ≤\n        (4 / cutExponent) / (D : ℝ) := by\n  filter_upwards [eventually_nonunit_card_le, eventually_gt_atTop (1 : ℕ)]\n    with N H hN\n  intro D hD\n  have hNr : (1 : ℝ) < N := by exact_mod_cast hN\n  have hN0 := zero_lt_one.trans hNr\n  have hlog := log_pos hNr\n  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD\n  have hD0 : (0 : ℝ) < D := by linarith only [hDr]\n  have hcap : 2 * (N : ℝ) / (D : ℝ) ≤ (N : ℝ) := by\n    apply (div_le_iff₀ hD0).mpr\n    calc\n      _ ≤ (D : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right hDr hN0.le\n      _ = _ := mul_comm _ _\n  have hu := H (2 * (N : ℝ) / (D : ℝ))\n    (div_nonneg (mul_nonneg (by norm_num) hN0.le) hD0.le) hcap\n  have hn : 0 ≤ norm N := div_nonneg hlog.le hN0.le\n  calc\n    _ ≤ _ := mul_le_mul_of_nonneg_left hu hn\n    _ = _ := by\n      unfold ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass.norm\n      field_simp [hN0.ne', hlog.ne', hD0.ne', cutExponent_pos.ne'] <;> ring\n\nend\nend ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient\n"}]
IMMUTABLE_PINS={'/workspace/p29-radial-profile-verification-20261125-pinbind-v4/VALIDATION_RESULTS.json': '5742156c6b46da61149f1355c0bbe33b22cb54d803ad33b4346c1c9d6c42051f', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/SOURCE_AND_OUTPUTS_AFTER.json': '9a38a315c2bbac38f5a85ea10b0051c80358bd08fe2a66128bf4d1e0d848f0a4', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/consumer-actual-imports-bindings.json': 'f99a3aea2dc3b103e793dfe1f96cc7cbac0897ba3ec053b077bdbb7021e78de8', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/BORROWED_OBJECTS.json': '01f254264580b22f22c2e20caaba30b13d309656099d7127f49e2d6cb5022562', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/P2_CURRENT_P1_QUALIFICATION.json': 'e4eded9de6f8f361de93da40e9615eb0e75e7ce05e110561ca08ea4b7151bc19', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/P1_FIVE_IMPORT_COMPARISON.json': 'c28904e9a8c3dd671128810c1dd513bdd61ae6197944691b573652db6a65fbb1', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/PP_MAX_STEPS_RESOLUTION.json': '9784a1c67167e9d67861d0fde85b9d8a5a0eb2df496ea0d81d374bb4b6dbaabb', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/driver.py': 'ceb4f796dc7a362e47ae49fb0a2300f425c769500610e7c8baa09a6580b2170e', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/driver-pp1e6-resume.py': 'fad03cf7d93979bdaab9dfb681089ea1bc581a31860b0f469b0c59bcb140964a', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-evidence/state.json': '93dd7569b9434e6c5bc4a795fb194f7050dc8f9eee8eaf8fea15df56b3fe0bec', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-evidence/audit.json': '9bd091734012e9e8c38b1d4c5d792ec5a55f2ea18aee3ca40a368afd059c77d1', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/runtime-evidence/compiler-commands.jsonl': '67e08b94cda9b21cb7ee91ac58ee591f5f7619dd4e9fe8cbff5cf2d3f6861b42', '/workspace/p29-radial-profile-verification-20261125-pinbind-v4/FAILURE.json': 'ec27af46c62c1b54f95d1da40fc797944ebeb64b2972ad8aae692bcf5870e22e', '/workspace/p29-radial-profile-20261125-pinbind-v4/lakefile.toml': '70ab0b7423ca1c3cbf690573ecaf580e2290ff9ad5c59015b556e068d415e2ff', '/workspace/p29-radial-profile-20261125-pinbind-v4/lake-manifest.json': '0c1ed2f4476d4b54d5376b98606e861fd7ecc822ddf3977831f48469c83fc54b', '/workspace/p29-radial-profile-20261125-pinbind-v4/lean-toolchain': '62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef', '/workspace/p29-nonunit-supply-20261125-0238173d/BINDING_RECEIPT.json': 'c70b4abe99b6335384c42c05e241611979a6da1119cf1e4883ee87dee42b3788', '/workspace/p29-nonunit-supply-20261125-0238173d/VALIDATION_RESULTS.json': '9664afeec28214c01e08d54c36a8effc1259f5beb50e2c00389c58f1b490da29', '/workspace/p29-nonunit-supply-20261125-0238173d/SOURCE_AND_OUTPUTS_AFTER.json': '94dfaa2d15bb5d4c7687b1289636b207175676f9173a4e41e4759b57616c39bc', '/workspace/p29-nonunit-supply-20261125-0238173d/controller-evidence/ACTUAL_IMPORT_PART_BINDINGS.json': 'c031a7e3c5773ecdf934bb8d286adbba917162bde305ede2b2fd0061765484d6', '/workspace/p29-nonunit-supply-20261125-0238173d/controller-evidence/PRODUCER_BINDINGS.json': '8009323d35bc0d3efd12b3199ba11b8aca608ef1081e4df71d5286f5e6f01277'}
RESUME_RECORD_PINS={'BORROWED_OBJECTS.json': {'bytes': 3990, 'sha256': 'b094949363cd7d4ecf896a0dde5988328d51a724f66a3e7cb3978930d0d5fd1f', 'stat': [27, 822934, 3990, 1795664135371982087, 1795664135371982087]}, 'CONFIGURATION_ADAPTATION.json': {'bytes': 661, 'sha256': '6d62c337e842dbce0e10b1b137ad619337300a85d44c9956b546dce1a539be0c', 'stat': [27, 822940, 661, 1795664135374456568, 1795664135374456568]}, 'EXACT_SUPPLIER_REUSE.json': {'bytes': 1175, 'sha256': 'f7008825549481e86f94a80a3849e802b12ab8e9f054ea8b9153006ef5948ca3', 'stat': [27, 822999, 1175, 1795664167543906190, 1795664167543906190]}, 'FAILURE.json': {'bytes': 710, 'sha256': '4d64b876632a3c568ca7a959f00300f769c25ac38696b2f7a8396f6736685d96', 'stat': [27, 823005, 710, 1795664175920948552, 1795664175920948552]}, 'INPUTS.json': {'bytes': 236, 'sha256': '809d723224e269feeb05d21e6cc0ee546009b7864d1cf9ae94027576728c2a0b', 'stat': [27, 822917, 236, 1795664116438765329, 1795664116438765329]}, 'LAKEFILE_EXACT_DIFF.patch': {'bytes': 623, 'sha256': 'a78117d913382d7ebe16deb2939feb3070b44464d74bb743114098f642430125', 'stat': [27, 822937, 623, 1795664135374040322, 1795664135374040322]}, 'ORIGINAL_NONUNIT_BINDING_RECEIPT.json': {'bytes': 2065, 'sha256': 'c70b4abe99b6335384c42c05e241611979a6da1119cf1e4883ee87dee42b3788', 'stat': [27, 822924, 2065, 1795664116440108745, 1795664116440108745]}, 'ORIGINAL_NONUNIT_SOURCE_AND_OUTPUTS_AFTER.json': {'bytes': 2853, 'sha256': '94dfaa2d15bb5d4c7687b1289636b207175676f9173a4e41e4759b57616c39bc', 'stat': [27, 822926, 2853, 1795664116440606414, 1795664116440606414]}, 'ORIGINAL_NONUNIT_VALIDATION_RESULTS.json': {'bytes': 41150, 'sha256': '9664afeec28214c01e08d54c36a8effc1259f5beb50e2c00389c58f1b490da29', 'stat': [27, 822925, 41150, 1795664116440199955, 1795664116440199955]}, 'ORIGINAL_P1_FAILURE.json': {'bytes': 847, 'sha256': 'ec27af46c62c1b54f95d1da40fc797944ebeb64b2972ad8aae692bcf5870e22e', 'stat': [27, 822923, 847, 1795664116440025912, 1795664116440025912]}, 'ORIGINAL_P1_GUARD_LOG.jsonl': {'bytes': 14310, 'sha256': '67e08b94cda9b21cb7ee91ac58ee591f5f7619dd4e9fe8cbff5cf2d3f6861b42', 'stat': [27, 822919, 14310, 1795664116439468077, 1795664116439468077]}, 'ORIGINAL_P1_LAKEFILE.toml': {'bytes': 2878, 'sha256': '70ab0b7423ca1c3cbf690573ecaf580e2290ff9ad5c59015b556e068d415e2ff', 'stat': [27, 822936, 2878, 1795664135373498240, 1795664135373498240]}, 'ORIGINAL_P1_RUNTIME_AUDIT.json': {'bytes': 288, 'sha256': '9bd091734012e9e8c38b1d4c5d792ec5a55f2ea18aee3ca40a368afd059c77d1', 'stat': [27, 822920, 288, 1795664116439682743, 1795664116439682743]}, 'ORIGINAL_P1_RUNTIME_STATE.json': {'bytes': 4780, 'sha256': '93dd7569b9434e6c5bc4a795fb194f7050dc8f9eee8eaf8fea15df56b3fe0bec', 'stat': [27, 822921, 4780, 1795664116439767839, 1795664116439767839]}, 'ORIGINAL_P1_VALIDATION_RESULTS.json': {'bytes': 15032, 'sha256': '5742156c6b46da61149f1355c0bbe33b22cb54d803ad33b4346c1c9d6c42051f', 'stat': [27, 822922, 15032, 1795664116439840844, 1795664116439840844]}, 'PINNED_TOOLCHAIN.json': {'bytes': 1330, 'sha256': '0df5ac3729a2e6651abb7062a3218925cec9105b07959502cb9037278ebf34a8', 'stat': [27, 822994, 1330, 1795664142193091961, 1795664142193091961]}, 'PRIOR_EVIDENCE_PINS.json': {'bytes': 8182, 'sha256': 'c9d2094fa5634a36a73fb4dc38ca7a5c9f72e5f3b8afc67ea3c1438eb86051b4', 'stat': [27, 822918, 8182, 1795664116439080377, 1795664116439080377]}, 'driver.py': {'bytes': 41009, 'sha256': 'c970948d0848815c2d8dd4462c506e6842efc60415df5b2a9bfc3e14c881ebba', 'stat': [27, 822915, 41009, 1795664116438428573, 1795664116438428573]}, 'merged-supplier-actual-imports-bindings.json': {'bytes': 65991687, 'sha256': '74a28fe0612de36a7d4df66f78af7ad5207288ec2cdf7054fc2112e75b597c69', 'stat': [27, 822998, 65991687, 1795664167163911621, 1795664167163911621]}, 'merged-supplier-actual-imports-process.json': {'bytes': 2085, 'sha256': '54c17dd6b88c1118ea4a65b3d7ed7ce0f06cf2127bf84f77e140dc0b10a61b9e', 'stat': [27, 822997, 2085, 1795664164672043221, 1795664164672043221]}, 'merged-supplier-actual-imports.lean': {'bytes': 1311, 'sha256': 'b46d020ddb430dc0c65e2049abd44f091691c0c90372971c74a3cd8acb07c225', 'stat': [27, 822995, 1311, 1795664142193171219, 1795664142193171219]}, 'merged-supplier-actual-imports.log': {'bytes': 9585390, 'sha256': 'c4dd9321ef29bd9a393bf4fcab6cae0dd506261018bb780cb4a61b9a09564676', 'stat': [27, 822996, 9585390, 1795664164403951070, 1795664164403951070]}, 'normal-build-process.json': {'bytes': 3378, 'sha256': 'e37e2b4dd43ad861d871b34f89a2b6e0e7ebc40dfb8fe88088ad55a9ed082f46', 'stat': [27, 823004, 3378, 1795664175225166526, 1795664175225166526]}, 'normal-build.log': {'bytes': 2516, 'sha256': '6ad87fee24189ac21473fd16d55e18daa50b34e64d7873914ca4fc5f6f1e27b5', 'stat': [27, 823000, 2516, 1795664175083797244, 1795664175083797244]}, 'pinned-lean-prefix-process.json': {'bytes': 1779, 'sha256': '492f8779caa59d5225a17355b56e6276c057092ea3dcee25e398bd34d3d74689', 'stat': [27, 822993, 1779, 1795664142192403943, 1795664142192403943]}, 'pinned-lean-prefix.log': {'bytes': 80, 'sha256': '32bec561d36abd6e7f08142788164aaeda386c376fba0a928a2c8a00c10ba4b5', 'stat': [27, 822992, 80, 1795664142080271642, 1795664142080271642]}, 'pinned-lean-version-process.json': {'bytes': 1766, 'sha256': 'e4d31cf279c3df2e61f0b73fad605f494738f2b58242b7c1b936effebcc4eee7', 'stat': [27, 822991, 1766, 1795664141389279188, 1795664141389279188]}, 'pinned-lean-version.log': {'bytes': 110, 'sha256': 'ae146854170a6cd1a13fc8fc6b3b596871cfda4f6cdb614884b2af5f7e9e5ed1', 'stat': [27, 822990, 110, 1795664141264284706, 1795664141264284706]}, 'runtime-evidence/audit.json': {'bytes': 287, 'sha256': '91f0d8c0fa805fec7cb87f5eb356ff23962f50415c9deeb367e5d314491b5507', 'stat': [27, 822988, 287, 1795664140427439910, 1795664140427439910]}, 'runtime-evidence/clang-wrapper.py': {'bytes': 6512, 'sha256': '4e3b74c52e1de8df2a291f45c90b672907f3b9b4f8423982ab3187ae2d718e9f', 'stat': [27, 822966, 6512, 1795664135542540673, 1795664135542639362]}, 'runtime-evidence/compiler-commands.jsonl': {'bytes': 6102, 'sha256': 'd4c1c66275a5aeda8ac403bf01c0a2bac001236dcbfb74f90a1bd5f00aff0df1', 'stat': [27, 822971, 6102, 1795664170487864047, 1795664170487864047]}, 'runtime-evidence/compiler.lock': {'bytes': 0, 'sha256': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'stat': [27, 822977, 0, 1795664135780369541, 1795664135780369541]}, 'runtime-evidence/lean-wrapper.py': {'bytes': 6512, 'sha256': '4e3b74c52e1de8df2a291f45c90b672907f3b9b4f8423982ab3187ae2d718e9f', 'stat': [27, 822962, 6512, 1795664135540740567, 1795664135541022293]}, 'runtime-evidence/leanc-wrapper.py': {'bytes': 6512, 'sha256': '4e3b74c52e1de8df2a291f45c90b672907f3b9b4f8423982ab3187ae2d718e9f', 'stat': [27, 822968, 6512, 1795664135543517867, 1795664135543702949]}, 'runtime-evidence/leanir-wrapper.py': {'bytes': 6512, 'sha256': '4e3b74c52e1de8df2a291f45c90b672907f3b9b4f8423982ab3187ae2d718e9f', 'stat': [27, 822964, 6512, 1795664135541733561, 1795664135541918377]}, 'runtime-evidence/llvm-ar-wrapper.py': {'bytes': 6512, 'sha256': '4e3b74c52e1de8df2a291f45c90b672907f3b9b4f8423982ab3187ae2d718e9f', 'stat': [27, 822970, 6512, 1795664135544282880, 1795664135544371783]}, 'runtime-evidence/state.json': {'bytes': 4763, 'sha256': 'dc612ac463b5744fce50ce6cb89a1f4d5fab1343c7e089645a9c06182e058f20', 'stat': [27, 822972, 4763, 1795664135544860021, 1795664135544860021]}, 'runtime-initial-audit-process.json': {'bytes': 3014, 'sha256': 'ecff9c2b49ab1c88e2b75e0998fddd307d8959dcc892481c102608977dc16dac', 'stat': [27, 822989, 3014, 1795664140584295595, 1795664140584295595]}, 'runtime-initial-audit.log': {'bytes': 499, 'sha256': 'd21b6eff3ce3d9b59b3be28a82575b2a24784bded266ebf46eb567db2093d3bf', 'stat': [27, 822976, 499, 1795664140427439910, 1795664140427439910]}, 'runtime-setup-process.json': {'bytes': 447, 'sha256': 'fddc358d0f00543130af2d51f9d114a8018ab1fbf76cf3b17c5e1ea18a725204', 'stat': [27, 822975, 447, 1795664135553816934, 1795664135553816934]}, 'runtime-setup.log': {'bytes': 326, 'sha256': '0d86b0abc1defe6b9b69e1b6d4f48b7400e3dcac89a6904fc407f5d93239fa24', 'stat': [27, 822944, 326, 1795664135544971097, 1795664135544971097]}, 'runtime.env': {'bytes': 288, 'sha256': '766401cf3273bcfecc316081c2b3ce5070127b12872cbcadef6ec156015215c8', 'stat': [27, 822973, 288, 1795664135544938435, 1795664135544938435]}, 'runtime.path': {'bytes': 84, 'sha256': '961f9419e0fab3c575767a97a2ab5e0c35e6b7365a52b92370d07e6d5e7d919c', 'stat': [27, 822974, 84, 1795664135544971097, 1795664135544971097]}}
PIN='leanprover/lean4:v4.33.0-rc1'
LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux').resolve()
TOOL_LIB=(TC/'lib/lean').resolve()
package_revisions={'mathlib':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','plausible':'b1c4a69a7e247ab7df20460212001673d74f08c0','LeanSearchClient':'0498c7c070c143a3bf7379f4d99a2c63bb9d9715','importGraph':'18a90119a5d316358fde6c86e0ca24e59212e32c','proofwidgets':'b1436dc749e722c9920036b52cdc43b3451d0b69','aesop':'57d3325be72a842920813bcb40f96a6f7393c185','Qq':'ee41917ae11d38479fb8fb24745f7ca4bf0a784d','batteries':'41bd267b3f6b7252f6676af46d4ffc6783b64de9','Cli':'da07ca808b6718cb2aed14dba154e5a08b8f8ecf'}
GUARD=P('/workspace/goldbach-formalization/docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/ci_runtime_guard.py')
RUNNER=P('/workspace/blue-build-tools/run_guarded.py')
OWNED=P('/workspace/blue-build-tools/validate_member_roots_owned.py')
tools_expected={str(GUARD):'837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877',str(RUNNER):'c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526',str(OWNED):'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'}
direct_imports=['ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass','MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform']
project_suppliers=['ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants','ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass']
native_modules=['MathlibNt.Wu2008DoubleSieve.NonunitRoughUniformCore','MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform']

root=P('/workspace/p29-nonunit-quotient-20261126-0117dd4')
attempt1=P('/workspace/p29-nonunit-quotient-verification-20261126-0117dd4')
out=attempt1/'norm-fqn-002'
priorroot=P('/workspace/p29-radial-profile-20261125-pinbind-v4')
priorout=P('/workspace/p29-radial-profile-verification-20261125-pinbind-v4')
nativeout=P('/workspace/p29-nonunit-supply-20261125-0238173d')
assert not out.exists(),'Do not repeat a submitted target-only resume.'
assert sha(attempt1/'driver.py')=='c970948d0848815c2d8dd4462c506e6842efc60415df5b2a9bfc3e14c881ebba'
for name,rec in RESUME_RECORD_PINS.items():
 p=attempt1/name;assert p.stat().st_size==rec['bytes']and sha(p)==rec['sha256']and stamp(p)==rec['stat'],('Original failed run changed',name)
assert all(sha(p)==h for p,h in IMMUTABLE_PINS.items())
assert all(sha(p)==h for p,h in tools_expected.items())
prior_pin_stamps={p:stamp(p)for p in IMMUTABLE_PINS}
oldtree=ast.parse((priorout/'driver.py').read_text())
old_literals={n.targets[0].id:ast.literal_eval(n.value)for n in oldtree.body if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)and isinstance(n.value,ast.Constant)}
AUDIT_TEMPLATE=json.loads(old_literals['AUDIT_TEXT'])
mods=[r['module']for r in INPUTS];assert mods==['ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient']
target=root/(mods[0].replace('.','/')+'.lean')
old_source=target.read_bytes();assert len(old_source)==3380 and hashlib.sha256(old_source).hexdigest()=='6b11d4a2bc7838dbdda9e1354b796f659d7782dbd3d62fcec372f49f898611ef'
new_source=INPUTS[0]['source'].encode();assert len(new_source)==3431 and hashlib.sha256(new_source).hexdigest()==INPUTS[0]['sha256']
assert hashlib.sha1(b'blob '+str(len(new_source)).encode()+b'\0'+new_source).hexdigest()==INPUTS[0]['blob']
old_line=b'      unfold norm\n';new_line=b'      unfold ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass.norm\n'
assert old_source.count(old_line)==1 and new_source==old_source.replace(old_line,new_line,1)and new_source.replace(new_line,old_line,1)==old_source
assert re.findall(r'(?m)^import ([A-Za-z0-9_.]+)$',new_source.decode())==direct_imports
lib=root/'.lake/build/lib/lean';rel=mods[0].replace('.','/')
for q in [lib/(rel+s)for s in ['.olean','.ilean','.trace']]+[root/'.lake/build/ir'/(rel+'.c')]:assert not q.exists(),('Already produced output; do not repeat normal',q)
failed_setup=root/'.lake/build/ir'/(rel+'.setup.json')
assert failed_setup.stat().st_size==2658625 and sha(failed_setup)=='33c54776d6f0c9a4fc1973e688606a7bc6ed0cad08fbf81b698f75faace91c6c'
failure=json.loads((attempt1/'FAILURE.json').read_text())
assert failure['completed_stages']==['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','merged-supplier-actual-imports','normal-build']
assert failure['old_evidence_changed']==failure['borrowed_cache_changed']==[]
normal1=json.loads((attempt1/'normal-build-process.json').read_text());assert normal1['exit_code']==1 and normal1['forbidden_source_calls']==[]
assert normal1['log_sha256']==sha(attempt1/'normal-build.log')
assert 'ambiguous term' in(attempt1/'normal-build.log').read_text()and ':72:13:'in(attempt1/'normal-build.log').read_text()
state_path=attempt1/'runtime-evidence/state.json';state=json.loads(state_path.read_text());state_sha_before=sha(state_path)
guardlog=P(state['log']);original_guard_prefix=guardlog.read_bytes()
assert len(original_guard_prefix)==6102 and hashlib.sha256(original_guard_prefix).hexdigest()=='d4c1c66275a5aeda8ac403bf01c0a2bac001236dcbfb74f90a1bd5f00aff0df1'
assert original_guard_prefix.endswith(b'\n')
old_commands=[json.loads(l)for l in original_guard_prefix.splitlines()if l]
old_source_calls=[str((P(r['cwd'])/a).resolve())if not P(a).is_absolute()else str(P(a).resolve())for r in old_commands if r.get('tool')=='lean'for a in r.get('input_args',[])if str(a).endswith('.lean')]
assert old_source_calls==[str(target.resolve())]
allowed_sources={str(target.resolve())}
runprefix=['python3',str(RUNNER),'--state',str(state_path)]
assert normal1['command']==runprefix+['lake','build','+'+mods[0]+':olean']
assert state['policy']==json.loads((priorout/'runtime-evidence/state.json').read_text())['policy']
config_before={str(root/name):sha(root/name)for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
assert config_before==state['input_sha256']
for key in ['runtime_sha256','input_sha256','action_script_sha256']:
 for p,h in state[key].items():assert sha(p)==h
release_binding=json.loads((attempt1/'PINNED_TOOLCHAIN.json').read_text())
assert release_binding['pin']==PIN and release_binding['lean_commit']==LEAN_COMMIT and release_binding['guarded_shadow']['state_sha256']==state_sha_before
assert P(state['realbin'])==(TC/'bin').resolve()and(P(state['shadow'])/'lib/lean').resolve()==TOOL_LIB
for label in ['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','merged-supplier-actual-imports']:
 rec=json.loads((attempt1/(label+'-process.json')).read_text());assert rec['exit_code']==0 and rec.get('forbidden_source_calls')==[]and rec['log_sha256']==sha(attempt1/(label+'.log'))
import_process=json.loads((attempt1/'merged-supplier-actual-imports-process.json').read_text())
audit_code=compile_audit_text(direct_imports)
assert import_process['command']==runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin']
assert import_process['stdin_sha256']==hashlib.sha256(audit_code).hexdigest()==sha(attempt1/'merged-supplier-actual-imports.lean')
reuse=json.loads((attempt1/'EXACT_SUPPLIER_REUSE.json').read_text())
assert reuse['status']=='PASS_EXACT_MERGED_INPUTS_WITHOUT_SUPPLIER_REPLAY'and reuse['actual_bindings_sha256']==sha(attempt1/'merged-supplier-actual-imports-bindings.json')
assert reuse['actual_bindings_sha256']=='74a28fe0612de36a7d4df66f78af7ad5207288ec2cdf7054fc2112e75b597c69'
before=json.loads((attempt1/'merged-supplier-actual-imports-bindings.json').read_text())
assert before['roots']==direct_imports and before['module_count']==6184 and before['part_count']==30820 and len(before['parts'])==30820
cache_before={};protected_outputs={};knownparts={};expected_hashes={};expected_authorities={};package_bindings={}
for part in before['parts']:
 p=part['identity']['path'];assert stamp(p)==part['stat_snapshot'],('Previously passed union facet changed',p)
 assert part['facet']==facet_of(part['module'],p)
 accept_part(part['module'],part['identity'],part['stat_snapshot'],part['authority'])
 if part['requested_path']in knownparts:assert knownparts[part['requested_path']]['identity']['sha256']==part['identity']['sha256']
 else:knownparts[part['requested_path']]=knownparts[p]
hashes_before=dict(expected_hashes);assert len(hashes_before)==30820
borrows=json.loads((attempt1/'BORROWED_OBJECTS.json').read_text())['objects'];assert set(borrows)==set(project_suppliers)
for module,row in borrows.items():
 assert sha(row['source'])==row['source_sha256']and sha(row['object'])==row['object_sha256']==expected_hashes[(module,'.olean')]
 for path,h in [(row['source'],row['source_sha256']),(row['object'],row['object_sha256']),(row['original_object'],row['object_sha256'])]:
  assert sha(path)==h;cache_before[path]=stamp(path);protected_outputs[path]={'bytes':P(path).stat().st_size,'sha256':h}
native_receipt=json.loads((nativeout/'BINDING_RECEIPT.json').read_text())
assert native_receipt['status']=='PASS_CURRENT_P1_EXISTING_NONUNIT_SUPPLY'
for prior in [priorout,nativeout]:
 for path,row in json.loads((prior/'SOURCE_AND_OUTPUTS_AFTER.json').read_text()).items():
  assert P(path).stat().st_size==row['bytes']and sha(path)==row['sha256'];protected_outputs[path]=row;cache_before[path]=stamp(path)
for p,h in state['runtime_sha256'].items():assert sha(p)==h;cache_before[p]=stamp(p)
out.mkdir();(out/'driver.py').write_text(SOURCE_TEXT)
(out/'ORIGINAL_SOURCE_001.lean').write_bytes(old_source)
shutil.copyfile(failed_setup,out/'ORIGINAL_FAILED_TARGET_SETUP.json')
(out/'ORIGINAL_GUARD_PREFIX.jsonl').write_bytes(original_guard_prefix)
shutil.copyfile(attempt1/'runtime-evidence/audit.json',out/'ORIGINAL_INITIAL_RUNTIME_AUDIT.json')
save(out/'INPUTS.json',[{k:v for k,v in row.items()if k!='source'}for row in INPUTS])
save(out/'RESUME_CONTEXT.json',{'schema':'p29_nonunit_norm_fqn_target_only_resume_v1','original_job':'job_32004ceec6c8421a9d69def635904982','readonly_snapshot_job':'job_b047247ff40e4a249b2f8c29bfcb3ba3','readonly_snapshot_git_blob':'74e9ef96df88330adaaefce79c3f0d53f5cba16c','original_source_blob':'0117dd4f635e04bed4a5191f06295a442975a0b4','new_source_blob':INPUTS[0]['blob'],'single_FQN_inverse_restores_original_file':True,'public_statements_and_other_proof_bytes_unchanged':True,'original_normal_failure_sha256':sha(attempt1/'normal-build.log'),'original_guard_prefix_bytes':len(original_guard_prefix),'original_guard_prefix_sha256':hashlib.sha256(original_guard_prefix).hexdigest(),'original_state_sha256':state_sha_before,'reused_union_bindings_sha256':sha(attempt1/'merged-supplier-actual-imports-bindings.json'),'reused_exact_union_receipt_sha256':sha(attempt1/'EXACT_SUPPLIER_REUSE.json'),'passed_union_modules':6184,'passed_union_facets':30820,'supplier_probe_repeated':False,'old_kernel_replays':0,'old_owned_replays':0,'guard_setup_repeated':False,'original_record_pins':RESUME_RECORD_PINS,'normal_warning_as_error_requested':False,'normal_attempts_before_resume':1})
target.write_bytes(new_source);assert sha(target)==INPUTS[0]['sha256']
runtime_parent=root/'runtime';base_env=os.environ.copy()
for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR='/workspace/blue-build-tools/lean-action',GITHUB_ENV=str(attempt1/'runtime.env'),GITHUB_PATH=str(attempt1/'runtime.path'))
base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
runs=[];sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED);auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)

try:
 normal=stage('normal-build',runprefix+['lake','build',*['+'+m+':olean'for m in mods]],allow_sources=allowed_sources)
 production=source_outputs();assert production[str(target)]['sha256']==INPUTS[0]['sha256'];save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',production)
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
 assert guardlog.read_bytes().startswith(original_guard_prefix)
 assert len(source_calls)==2 and source_calls==old_source_calls+[str(target.resolve())],source_calls
 for name,rec in RESUME_RECORD_PINS.items():
  if name not in ['runtime-evidence/compiler-commands.jsonl','runtime-evidence/audit.json','runtime-evidence/compiler.lock']:
   p=attempt1/name;assert p.stat().st_size==rec['bytes']and sha(p)==rec['sha256'],('Original first-run evidence changed',name)
 normal_warnings=[line for line in(out/'normal-build.log').read_text().splitlines()if line.startswith('warning:')]
 save(out/'SOURCE_AND_OUTPUTS_AFTER.json',final)
 result={'schema':'p29_nonunit_quotient_original_source_normal_kernel_full_owned_v1','result':'PASS_ONE_NEW_NONUNIT_QUOTIENT_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED','root':str(root),'evidence':str(out),'modules':mods,'inputs':[{k:v for k,v in row.items()if k!='source'}for row in INPUTS],'normal':normal,'normal_warning_as_error_requested':False,'normal_warning_count':len(normal_warnings),'normal_warnings':normal_warnings,'kernel':kernel,'owned':owned,'stock':stock,'owned_declarations':len(decls),'owned_declaration_counts':inventory['module_counts'],'observed_axioms':axioms,'full_owned_private_generated_ast_universes':True,'actual_import_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'before_actual_import_bindings_sha256':sha(attempt1/'merged-supplier-actual-imports-bindings.json'),'exact_supplier_reuse_receipt_sha256':sha(attempt1/'EXACT_SUPPLIER_REUSE.json'),'consumer_setup_import_match_sha256':sha(out/'CONSUMER_SETUP_IMPORT_MATCH.json'),'normal_source_invocations':source_calls,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'prior_evidence_and_old_runtime_unchanged':True,'old_source_recompilations':0,'old_kernel_replays':0,'old_owned_replays':0,'old_supplier_new_formal_credit':0,'native_supplier_type_representation':native_receipt['type_representation'],'new_actual_external_authorities':0,'runtime_policy':state['policy'],'original_audited_tools_unchanged':tools_expected,'scope_note':'Existing frozen Gamma5 nonunit real-height count and inverse-product quotient bound only. No new manuscript-external statement, aggregate wall payment, signed PP estimate, or full P2.9 conclusion is claimed.'}
 result.update(original_failure_retained=True,normal_attempts_total=2,original_failed_normal_attempts=1,new_successful_normal_attempts=1,source_repair='one proof-only fully qualified norm',supplier_import_probe_repeated=False,guard_setup_repeated=False,reused_union_bindings_sha256=sha(attempt1/'merged-supplier-actual-imports-bindings.json'),resume_context_sha256=sha(out/'RESUME_CONTEXT.json'))
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','root','evidence','modules','owned_declarations','owned_declaration_counts','observed_axioms','normal_warning_as_error_requested','normal_warning_count','monitored_parts_unchanged']}),flush=True)
 print(json.dumps({'validation_results_sha256':sha(out/'VALIDATION_RESULTS.json'),'source_outputs_sha256':sha(out/'SOURCE_AND_OUTPUTS_AFTER.json'),'declarations_sha256':sha(out/'full-owned-DECLARATION_TYPES_AXIOMS.json'),'inventory_sha256':sha(out/'full-owned-INVENTORY_NAME_SET_CHECK.json')}),flush=True)

except Exception as e:
 failure={'schema':'p29_nonunit_norm_fqn_002_resume_failure_v1','root':str(root),'evidence':str(out),'error':str(e),'traceback':traceback.format_exc(),'completed_resume_stages':[r['stage']for r in runs],'original_failure_sha256':sha(attempt1/'FAILURE.json'),'supplier_probe_repeated':False,'borrowed_cache_changed':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s]}
 save(out/'FAILURE.json',failure);print(json.dumps(failure),flush=True);raise

export=out/'portable';export.mkdir()
entries={'evidence/'+str(p.relative_to(out)):p for p in out.rglob('*')if p.is_file()and export not in p.parents}
for name in RESUME_RECORD_PINS:
 if name not in ['runtime-evidence/compiler-commands.jsonl','runtime-evidence/audit.json','runtime-evidence/compiler.lock']:
  entries['original-attempt-001/'+name]=attempt1/name
entries['runtime-evidence/final-state.json']=state_path
entries['runtime-evidence/final-guard-log.jsonl']=guardlog
entries['runtime-evidence/final-runtime-audit.json']=attempt1/'runtime-evidence/audit.json'
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
