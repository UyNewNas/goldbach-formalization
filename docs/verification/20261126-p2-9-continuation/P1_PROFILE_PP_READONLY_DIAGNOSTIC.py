from pathlib import Path
import ast,hashlib,json
root=Path('/workspace/p29-radial-profile-20261125-pinbind-v4')
out=Path('/workspace/p29-radial-profile-verification-20261125-pinbind-v4')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def stamp(p):
 s=Path(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def record(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
driver=out/'driver.py'
assert sha(driver)=='ceb4f796dc7a362e47ae49fb0a2300f425c769500610e7c8baa09a6580b2170e'
tree=ast.parse(driver.read_text())
literal={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and isinstance(n.value,ast.Constant)}
inputs=json.loads(literal['INPUT_TEXT'])
logpath=out/'borrowed-full-owned.log';raw=logpath.read_text()
rows=[];issues=[];other_ellipsis=[];pretty_budget=1000000
for lineno,line in enumerate(raw.splitlines(),1):
 if line.startswith('MEMBER_OWNED_DECL '):
  r=json.loads(line.removeprefix('MEMBER_OWNED_DECL '));rows.append(r)
  for key,value in r.items():
   if isinstance(value,str)and('⋯'in value or '...'in value):
    positions=[i for i,c in enumerate(value)if c=='⋯']
    positions += [i for i in range(len(value)-2)if value[i:i+3]=='...']
    issue={'name':r.get('name'),'module':r.get('module'),'kind':r.get('kind'),'field':key,'characters':len(value),'ellipsis_count':len(positions),'snippets':[value[max(0,i-160):i+161]for i in positions[:4]],'value_sha256':hashlib.sha256(value.encode()).hexdigest(),'raw_AST_characters':len(r.get('type_expression','')),'raw_AST_ellipsis':('⋯'in r.get('type_expression','')or '...'in r.get('type_expression',''))}
    if len(value)<=pretty_budget:issue['complete_original_field_value']=value;pretty_budget-=len(value)
    else:issue['field_not_emitted_due_to_transport_budget']=True
    issues.append(issue)
 elif '⋯'in line or '...'in line:other_ellipsis.append({'line':lineno,'text':line[:2000]})
stages={}
for label in ['runtime-setup','runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','borrowed-actual-imports','borrowed-named-kernel','borrowed-full-owned']:
 p=out/(label+'-process.json');r=json.loads(p.read_text())
 if 'log_path'in r:assert sha(r['log_path'])==r['log_sha256']
 else:assert sha(out/(label+'.log'))==r['log_sha256']
 stages[label]={'identity':record(p),'record':r}
borrowed=json.loads((out/'BORROWED_OBJECTS.json').read_text())
bindings=json.loads((out/'borrowed-actual-imports-bindings.json').read_text())
changed_parts=[]
for p in bindings['parts']:
 path=p['identity']['path']
 if not Path(path).is_file()or stamp(path)!=p['stat_snapshot']:changed_parts.append(path)
state_path=out/'runtime-evidence/state.json';state=json.loads(state_path.read_text())
guard=Path(state['log']);commands=[json.loads(l)for l in guard.read_text().splitlines()if l]
source_calls=[r for r in commands if r.get('tool')=='lean'and any(str(x).endswith('.lean')for x in r.get('input_args',[]))]
targets=[]
for r in inputs:
 src=root/(r['module'].replace('.','/')+'.lean')
 expected=r['sha256'];assert sha(src)==expected
 output_paths=[root/'.lake/build/lib/lean'/(r['module'].replace('.','/')+s)for s in ['.olean','.ilean','.trace']]
 output_paths += [root/'.lake/build/ir'/(r['module'].replace('.','/')+s)for s in ['.c','.setup.json']]
 targets.append({'module':r['module'],'source':record(src),'expected_blob':r['blob'],'existing_output_paths':[str(p)for p in output_paths if p.exists()]})
tools={
 '/workspace/goldbach-formalization/docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/ci_runtime_guard.py':'837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877',
 '/workspace/blue-build-tools/run_guarded.py':'c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526',
 '/workspace/blue-build-tools/validate_member_roots_owned.py':'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'}
for p,h in tools.items():assert sha(p)==h
options=Path('/workspace/toolchains/lean-4.33.0-rc1-linux/src/lean/Lean/PrettyPrinter/Delaborator/Options.lean')
opts=options.read_text().splitlines();option_snippets=[]
for i,line in enumerate(opts):
 if 'pp.maxSteps'in line:option_snippets.append({'line':i+1,'text':'\n'.join(opts[max(0,i-1):min(len(opts),i+6)])})
audit_source=out/'borrowed-full-owned.lean'
selected_files=['FAILURE.json','P1_FIVE_IMPORT_COMPARISON.json','CONFIGURATION_ADAPTATION.json','PINNED_TOOLCHAIN.json','BORROWED_OBJECTS.json','borrowed-actual-imports-bindings.json','borrowed-full-owned.lean']
identities={name:record(out/name)for name in selected_files}
summary={'schema':'p29_p1_profile_full_owned_read_only_diagnostic_v1','root':str(root),'evidence':str(out),'driver':record(driver),'log':record(logpath),'owned_rows':len(rows),'issue_count':len(issues),'issues':issues,'non_record_ellipsis':other_ellipsis,'all_raw_AST_fields_complete':all('⋯'not in r.get('type_expression','')and '...'not in r.get('type_expression','')for r in rows),'stages':stages,'failure':json.loads((out/'FAILURE.json').read_text()),'file_identities':identities,'p1_import_comparison':json.loads((out/'P1_FIVE_IMPORT_COMPARISON.json').read_text()),'configuration':json.loads((out/'CONFIGURATION_ADAPTATION.json').read_text()),'pinned_toolchain':json.loads((out/'PINNED_TOOLCHAIN.json').read_text()),'borrowed_modules':sorted(borrowed['objects']),'actual_modules':bindings['module_count'],'actual_parts':bindings['part_count'],'actual_parts_stat_changed':changed_parts,'state_identity':record(state_path),'state':state,'guard_log':record(guard),'prior_source_calls':source_calls,'target_sources_and_outputs':targets,'tools_checked':tools,'audit_option_lines':[x for x in audit_source.read_text().splitlines()if 'set_option'in x],'pinned_pretty_options':record(options),'pp_maxSteps_source':option_snippets,'no_Lean_calls':True,'no_existing_file_writes':True,'new_proof_credit':0}
print(json.dumps(summary,ensure_ascii=True))
