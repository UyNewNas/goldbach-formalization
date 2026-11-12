"""Static source/hash/adapter generation only. Never stages, imports or evaluates Lean."""
from pathlib import Path
import ast, copy, difflib, hashlib, json, os, re, subprocess, tomllib

BASE=Path('E:/timot/Documents/FilesForGPT/Myath')
OUT=Path(__file__).resolve().parent
RES=BASE/'output/resume-20261112'
FINE=RES/'t01/density-validation-v2'
P2=RES/'p2-validation-v3'
SCOPE=RES/'t01/y18-validation-scope'
NATIVE=BASE/'goldbach-variable-envelope/.lake/ntfs-source-backups-20261011/goldbach'
MAIN=BASE/'goldbach-proof-github-sync-20261110.git'
ENV={**os.environ,'GIT_NO_LAZY_FETCH':'1','GIT_ALLOW_PROTOCOL':'','GIT_TERMINAL_PROMPT':'0'}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def desc(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b)}
def dump(name,value):
 (OUT/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def write(name,s):
 p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s,encoding='utf-8',newline='\n')
def git_bytes(repo,args):
 cmd=['git','-c','remote.origin.promisor=false','-c','protocol.allow=never']
 cmd+=['--git-dir='+str(repo)] if repo==MAIN else ['-C',str(repo)]
 return subprocess.check_output(cmd+args,env=ENV,stderr=subprocess.PIPE)

gpath=RES/'t16-empty-review/y18-validation/GOLDBACH_ROOT_FIRST_COMPLETE_GRAPH.json'
graph=load(gpath);assert sha(gpath.read_bytes())=='d47f96073048f288dc225953b94e1c1fd5197c4f611ad15fa1a337878da6bf72'
bpath=RES/'t16-empty-review/y18-validation/REVIEW_BASES.json';bases=load(bpath)
project=load(SCOPE/'Y18_EXACT_SELECTED_PROJECT_SOURCES.json')
rows=project['selected_modules_in_import_order'];assert len(rows)==337
native=graph['rows'];assert len(native)==1348
research=[r for r in native if r['resolution']=='research_only'];standard=[r for r in native if r['resolution']!='research_only']
assert len(research)==460 and len(standard)==888
native_by={r['module']:r for r in native}
bare=sorted(r['module'] for r in research if '.' not in r['module']);assert len(bare)==7

# All selected native and shadow bytes are read from the fixed local Git object DB,
# with lazy fetching disabled. This is a metadata operation, not a native producer.
proc=subprocess.Popen(['git','-c','remote.origin.promisor=false','-c','protocol.allow=never','-C',str(NATIVE),'cat-file','--batch'],env=ENV,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
cache={}
def obj(oid):
 if oid not in cache:
  proc.stdin.write((oid+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().decode().split();assert len(h)==3 and h[1]=='blob',h
  b=proc.stdout.read(int(h[2]));assert proc.stdout.read(1)==b'\n' and blob(b)==oid;cache[oid]=b
 return cache[oid]
native_rows=[];shadow=[];native_mentions=[];empty_syntax=[]
for r in native:
 b=obj(r['blob']);assert len(b)==r['bytes'] and sha(b)==r['sha256']
 q={**r,'git_blob_sha1':r['blob'],'imports':r['direct_imports'],'origin':{'kind':'git','repository':graph['repo'],'commit':graph['commit'],'path':r['path']},'role':'research_mathematical_overlay' if r['resolution']=='research_only' else 'pinned_standard_dependency'}
 native_rows.append(q)
 if r['root_blob'] and r['research_blob'] and r['root_blob']!=r['research_blob']:
  a=obj(r['research_blob']);shadow.append({'module':r['module'],'selected_path':r['path'],'selected_sha256':sha(b),'selected_git_blob_sha1':r['blob'],'discarded_research_path':'research/wu2008/src/'+r['install_path'],'discarded_sha256':sha(a),'discarded_git_blob_sha1':r['research_blob'],'discarded_bytes':len(a),'authority':'Original09b standard lean_lib root path; actual guarded canonical source and setup must agree. No ABI equivalence asserted.'})
 text=b.decode('utf-8-sig')
 mentions=[{'line':i,'text':s.strip()} for i,s in enumerate(text.splitlines(),1) if re.search(r'\b(?:include_str|includeBin|include_bytes|readFile|readBinFile|IO\.FS\.)',s) or re.search(r'"[^"\n]+\.(?:json|npy|npz|bin)"',s)]
 if mentions:native_mentions.append({'module':r['module'],'mentions':mentions})
 if r['resolution']=='research_only' and not re.search(r'(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*(?:def|theorem|lemma|abbrev|structure|inductive|instance|opaque|axiom)\b',text):empty_syntax.append(r['module'])
proc.stdin.close();assert proc.wait()==0
assert len(shadow)==61
producer=load(RES/'t15-empty-mother/REGISTRY.json')['native_producer']
producer_checked=[]
for r in producer:
 match=[x for x in native_rows if x['path']==r['file']];assert len(match)==1
 q=match[0];assert q['git_blob_sha1']==r['blob'] and q['sha256']==r['sha256']
 producer_checked.append({'module':q['module'],'path':q['path'],'sha256':q['sha256'],'git_blob_sha1':q['git_blob_sha1'],'resolution':q['resolution']})

# Three exact project configuration files; project moreLeanArgs match Fine's
# frozen future-reuse profile, without changing the real memory/trust guard.
for name,oid in [('lean-toolchain','fd85b262bf1c734663aa8292b0101f672168788f'),('lake-manifest.json','86cb11a7a4b1c8ee3cd1d583985b4c7877933a4f'),('project-lakefile.toml','5891a201863f0edffc5028406724d6bc970cc892')]:
 b=git_bytes(MAIN,['cat-file','blob',oid]);assert blob(b)==oid;(OUT/name).write_bytes(b)
lock=load(OUT/'lake-manifest.json');architect=next(r for r in lock['packages'] if r['name']=='LeanArchitect')
assert architect['rev']=='78dd66840d3efe8c824c699fc03381cec817c271'
original=git_bytes(NATIVE,['show',graph['commit']+':lakefile.toml']);assert sha(original)=='fb01f3330623d8a6aa20e81e86b93da41df1272fd85f5528da6c9631e0e9822f'
(OUT/'goldbach-lakefile.original.toml').write_bytes(original)
native_config=original.decode()+'\n# Exact seven bare research suppliers; no new source or compiler options.\n'
for n in bare:native_config+='\n[[lean_lib]]\nname = "'+n+'"\nglobs = ["'+n+'"]\n'
write('goldbach-lakefile.y18.toml',native_config)
conf=tomllib.loads(native_config);prior=tomllib.loads(original.decode())
assert conf['lean_lib'][:len(prior['lean_lib'])]==prior['lean_lib']
assert {k:v for k,v in conf.items() if k!='lean_lib'}=={k:v for k,v in prior.items() if k!='lean_lib'}
assert [x['name'] for x in conf['lean_lib'][len(prior['lean_lib']):]]==bare

for rel,source in [('reused/ci_runtime_guard.py',P2/'reused/ci_runtime_guard.py'),('reused/Round6Audit.lean',P2/'reused/Round6Audit.lean')]:
 (OUT/rel).parent.mkdir(parents=True,exist_ok=True);(OUT/rel).write_bytes(source.read_bytes())

math_modules=[r['module'] for r in rows]+sorted(r['module'] for r in research)
assert len(math_modules)==len(set(math_modules))==797
floor=bases['original_floor'];assert len(floor)==len({r['name'] for r in floor})==17
# This is the exact P2 strict legacy audit transformation. In particular the
# FinitePi multiset mismatch diagnostic, flush, and rejection remain untouched.
audit=(P2/'reused/Round6Audit.lean').read_text(encoding='utf-8')
audit=audit[audit.index('set_option pp.all'):]
start=audit.index('  let modules := #[');end=audit.index('  let finalBridge :=',start)
audit=audit[:start]+'  let modules := #['+','.join('`'+n for n in math_modules)+']\n'+audit[end:]
audit=audit.replace('  if names.contains finalBridge then\n    throwError "Final bridge must not be included in the owned-module census"\n','').replace('(names.push finalBridge).qsort','names.qsort')
start=audit.index('    if name == finalBridge then');end=audit.index('  for (m, count) in counts do',start)
audit=audit[:start]+'    liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"\n'+audit[end:]
audit=audit.replace('  let finalBridge := `ImbalancedChen.current_theorem_1_1_of_manuscript_bounds\n','')
audit='\n'.join('import '+n for n in math_modules)+'\nimport Lean.Util.CollectAxioms\n'+audit
audit+='\n/- Exact original seventeen Y18 targets, independently reported by #print axioms. -/\n'
for r in floor:audit+='#print axioms '+r['name']+'\n'
write('CandidateAudit.lean',audit)
assert 'unless owned.qsort Name.lt == data.constNames.qsort Name.lt do' in audit
assert 'P0_ROUND6_INVENTORY_MISMATCH' in audit and '(← IO.getStdout).flush' in audit
assert audit.count('#print axioms ')==17

dump('PROJECT_SOURCE_SELECTION.json',project)
dump('NATIVE_SOURCE_SELECTION.json',{'schema':'Y18_PINNED_NATIVE_SOURCE_SELECTION_V1','status':'STATIC_SELECTED_BYTES_NO_OBJECT_ACCEPTANCE','revision':graph['commit'],'tree':graph['tree'],'source_graph':desc(gpath),'all_selected_native':native_rows,'research_overlays':[r for r in native_rows if r['role']=='research_mathematical_overlay'],'standard_dependency_modules':[r['module'] for r in standard],'shadow_variants':shadow,'bare_module_libraries':bare,'producer_anchor_matches':producer_checked,'data_read_source_mentions':native_mentions,'research_modules_without_obvious_declaration_syntax':empty_syntax,'no_producer_or_guard_executed':True})
dump('TARGET17.json',{'schema':'Y18_EXACT_ORIGINAL_TARGETS_V1','source':desc(bpath),'declarations':floor,'transitive_axioms_allowed':['propext','Classical.choice','Quot.sound'],'independent_print_axioms_required':True,'old_Fine_nine_targets_imported':False})

# Minimal hash-explicit configuration adaptation of the existing generic stage.
s=(P2/'reused/stage_p4.py').read_text(encoding='utf-8');s=s.replace("c7b839a2240d9960fb1f01f0e8808a9459935e0e","5891a201863f0edffc5028406724d6bc970cc892")
write('stage_p4_y18.py',s)

configs=[]
for name,path in [('lean-toolchain','lean-toolchain'),('lake-manifest.json','lake-manifest.json'),('project-lakefile.toml','lakefile.toml')]:
 d=desc(OUT/name);configs.append({**d,'path':name,'install_path':path,'git_blob':d['git_blob_sha1']})
manifest={'schema':'Y18_BOUNDED_VALIDATION_CANDIDATE_V1','status':'STATIC_CANDIDATE_NOT_DRIVER_READY','missing':[],
 'source_commit':project['source_publication'],'historical_assembly':'f1bcf37b6fe3f0a5a4b6c4c48b166a6119f9f784','native_rev':graph['commit'],
 'targets':[{'primary_module':'ImbalancedChen.P2GammaActualEmptyMotherPhysical','primary_modules':project['targets'],'closure_modules':[r['module'] for r in rows],
 'source_identity_sha256':sha(json.dumps([[r['module'],r['sha256']] for r in rows],separators=(',',':')).encode())}],
 'source_identity_recipe':'SHA256(UTF8(json.dumps([[module, sha256] for selected project rows in exact dependency order],separators=(comma,colon))))',
 'files':rows,'modules':[{**r,'source':r['install_path'],'git_blob':r['git_blob_sha1']} for r in rows],
 'project_modules':[r['module'] for r in rows],'native_sources':[r for r in native_rows if r['role']=='research_mathematical_overlay'],
 'all_native_sources':native_rows,'standard_native_modules':[r['module'] for r in standard],
 'mathematical_modules':math_modules,'audit_wrapper_modules':['CandidateAudit'],'fresh_kernel_modules':math_modules+['CandidateAudit'],
 'serialized_scope':{'project':337,'research':460,'total':797,'standard_dependency_not_individually_serialized':888},
 'kernel_scope':{'mathematical':797,'actually_built_wrapper':1,'total':798},
 'configuration':configs,'data_inputs':[],
 'source_data_statement':'All337 selected project texts contain no source-file data include/read mention. Full1348 native texts independently inventoried; any actual undeclared input remains fail-closed. No release bytes or numerical producer is rerun.',
 'native_configuration':{'original':{**desc(OUT/'goldbach-lakefile.original.toml'),'path':'goldbach-lakefile.original.toml'},'selected':{**desc(OUT/'goldbach-lakefile.y18.toml'),'path':'goldbach-lakefile.y18.toml'},'tracked_change_allowlist':['lakefile.toml'],'bare_libraries':bare,'source_override_allowlist':[]},
 'compiler_profiles':{'project':{'configuration':{**desc(OUT/'project-lakefile.toml'),'path':'project-lakefile.toml'},'moreLeanArgs':['-DmaxRecDepth=100000','-DmaxHeartbeats=4000000'],'definition_options':{'maxRecDepth':'100000','maxHeartbeats':'4000000'}},
 'goldbach':{'configuration':{**desc(OUT/'goldbach-lakefile.y18.toml'),'path':'goldbach-lakefile.y18.toml'},'moreLeanArgs':[],'definition_options':{},'selected_libraries':conf['lean_lib']},
 'wrapper':{'explicit_args':['-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-DwarningAsError=true'],'definition_options':{'maxRecDepth':'100000','maxHeartbeats':'4000000','warningAsError':'true'}}},
 'native_research_overlay':{'path':'NATIVE_SOURCE_SELECTION.json','sha256':sha((OUT/'NATIVE_SOURCE_SELECTION.json').read_bytes())},
 'audit_sources':[{**desc(OUT/'CandidateAudit.lean'),'path':'CandidateAudit.lean','install_path':'CandidateAudit.lean'}],
 'target_declarations':floor,'audit_external_imports':['Lean.Util.CollectAxioms'],
 'runtime_reuse':{**desc(OUT/'reused/ci_runtime_guard.py'),'path':'reused/ci_runtime_guard.py','trust':0,'threads':2,'memory_MiB':12288,'serial_flock':True},
 'locked_Architect':architect,'source_cache_accepted':False,'coherent_cache_accepted':False,'accepted_Stored32_in_scope':[],
 'FinitePi_gate':bases['old_strict_failure'],
 'open_before_root_driver':['Root external immutable driver selection and actual workflow binding are not constructed here.','T16 independent candidate review.','Root-supplied currentP2/R3 shared-failure selection must be checked before deployment; no unreviewed repair is silently substituted.','Real native guard/source/setup/import/facets, strict797 declarations, seventeen dual reports and798 fresh checker gates have not run.'],
 'driver_ready':False,'compiled':False,'kernel_verified':False,'whole_PP_or_K_accepted':False}
dump('Y18_MANIFEST.json',manifest)

# Keep complete mathematical and active standard source graphs distinct.
combined={r['module']:r['imports'] for r in rows+native_rows};seen=set();stack=[];order=[];front=set()
def visit(n):
 if n not in combined:front.add(n);return
 assert n not in stack,('Import cycle',n)
 if n in seen:return
 stack.append(n)
 for k in combined[n]:visit(k)
 stack.pop();seen.add(n);order.append(n)
for n in project['targets']:visit(n)
assert len(seen)==1685 and set(native_by)<=seen
dump('ACTUAL_IMPORT_GRAPH.json',{'project_targets':project['targets'],'project_count':337,'active_native_count':1348,'all_active_source_count':1685,'actual_combined_dependency_order':order,'strict_mathematical_order':math_modules,'fresh_checker_order':math_modules+['CandidateAudit'],'true_other_external_modules':sorted(front),'Architect_package':architect,'no_old_Fine_or_Stored_padding':True})
dump('STATIC_SOURCE_CHECKS.json',{'selected_project_sources':337,'historical_sources':335,'new_sources':2,'List_API_patches':13,'List_API_postimage_files':12,'research_overlays':460,'standard_native':888,'full_native':1348,'combined_reachable':len(seen),'native_shadow_variants':61,'bare_research_libraries':7,'strict_serialized_modules':797,'fresh_kernel_modules_with_wrapper':798,'exact_leaf_targets':17,'native_source_input_mentions':len(native_mentions),'research_without_obvious_declaration_syntax':empty_syntax,'locked_Architect_present':True,'data_producer_executed':False,'stage_Lean_or_guard_executed':False,'driver_ready':False})
print(json.dumps({'project':337,'native':1348,'research':460,'standard':888,'math':797,'checker':798,'target17':17,'native_input_mentions':len(native_mentions),'empty_research_syntax':empty_syntax,'true_other_external_count':len(front)},indent=2))
