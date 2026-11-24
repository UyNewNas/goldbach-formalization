from pathlib import Path
import ast,hashlib,json,collections,re,time

P=Path('/workspace/blue-member-build')
CODE=Path('/tmp/review_batch59_mechanical.py').read_text()
tree=ast.parse(CODE)
parser_nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='pretty_records']
for batch in [90]:
 R=Path('/workspace')/f'blue-member-repair-batch{batch}'
 outpath=Path('/tmp')/f'batch{batch}-mechanical-review.json'
 assert not outpath.exists(), 'Reuse a completed mechanical scan rather than repeat it.'
 cache={}
 def sha_file(path):
  path=Path(path);before=path.stat();token=lambda s:(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
  if str(path)in cache and cache[str(path)].get('stat_token')==list(token(before)):return cache[str(path)]
  h=hashlib.sha256()
  with path.open('rb')as f:
   while block:=f.read(1024*1024):h.update(block)
  assert token(before)==token(path.stat()),('changed while hashing',str(path))
  d={'path':str(path),'bytes':before.st_size,'sha256':h.hexdigest(),'stat_token':list(token(before))};cache[str(path)]=d;return d
 def decoded(s):
  for _ in range(3):
   t=re.sub(r'\\u([0-9a-fA-F]{4})',lambda m:chr(int(m.group(1),16)),s)
   t=re.sub(r'\\U([0-9a-fA-F]{8})',lambda m:chr(int(m.group(1),16)),t)
   t=t.replace('\\n','\n').replace('\\r','\r').replace('\\t','\t')
   if t==s:return t
   s=t
  return s
 def check_type(s):
  assert isinstance(s,str)and s
  dec=decoded(s)
  assert not any(x in dec for x in ['⋯','…','...','<maxRecDepth','<maxSteps','<maxHeartbeats']),('elision',dec[:100])
  return {'utf8_bytes':len(s.encode()),'sha256':hashlib.sha256(s.encode()).hexdigest(),'decoded_utf8_bytes':len(dec.encode()),'decoded_sha256':hashlib.sha256(dec.encode()).hexdigest(),'prefix':s[:80]}
 def summarize(d):
  for key in ['type','type_expression']:d[key]=check_type(d[key])
  return d
 # Reuse the already used one-field-at-a-time pretty-JSON reader, adding
 # decoded escape checks when its type summaries are independently compared.
 ns={'hashlib':hashlib,'json':json,'cache':cache}
 exec(compile(ast.Module(body=parser_nodes,type_ignores=[]),'existing-pretty-field-reader','exec'),ns)
 owned=ns['pretty_records'](R/'OWNED_EXPORTS.json')
 public=ns['pretty_records'](R/'PUBLIC_EXPORTS.json')
 for rows in [owned,public]:
  for row in rows:
   for key in ['type','type_expression']:
    assert row[key]['utf8_bytes']>0
    # SHA/length checks below are against independently decoded raw audit fields.
 records=[];names=None;footers={};total=None;rawhash=hashlib.sha256();offset=0
 raw_subset=[]
 with(R/'types-axioms.log').open('rb')as f:
  for line in f:
   rawhash.update(line)
   if line.startswith(b'AUDIT_RECORD '):
    d=json.loads(line[13:]);s=summarize(d)
    for key in ['type','type_expression']:
     expected=owned[len(records)][key]
     assert all(s[key][k]==expected[k]for k in ['utf8_bytes','sha256','prefix'])
     expected.update({k:s[key][k]for k in ['decoded_utf8_bytes','decoded_sha256']})
    assert d['kind']!='axiom'and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
    assert isinstance(d['universe_parameters'],list)
    d['transitive_axioms']=d['axioms'];d['is_axiom_declaration']=False
    records.append(d)
   elif line.startswith(b'MEMBER_OWNED_NAMES '):assert names is None;names=json.loads(line[19:])['names']
   elif line.startswith(b'MEMBER_OWNED_MODULE '):v=json.loads(line[20:]);assert v['module']not in footers;footers[v['module']]=v['count']
   elif line.startswith(b'MEMBER_OWNED_COUNT '):assert total is None;total=int(line[19:])
   else:assert not line.strip(),line[:200]
   offset+=len(line)
 cache[str(R/'types-axioms.log')]={'path':str(R/'types-axioms.log'),'bytes':offset,'sha256':rawhash.hexdigest()}
 assert records==owned
 pub_by_name={d['name']:d for d in public}
 for d in owned:
  if not d['is_private']:
   v=pub_by_name[d['name']]
   for key in ['type','type_expression']:
    assert all(v[key][k]==d[key][k]for k in ['utf8_bytes','sha256','prefix'])
    v[key].update({k:d[key][k]for k in ['decoded_utf8_bytes','decoded_sha256']})
 assert public==[d for d in owned if not d['is_private']]
 assert names==[d['name']for d in owned]and len(set(names))==len(names)==total
 result=json.loads((R/'VALIDATION_RESULTS.json').read_bytes());final=json.loads((R/'FINAL_RELEASE.json').read_bytes())
 selection=json.loads((R/'SOURCE_SELECTION.json').read_bytes());pubmanifest=json.loads((R/'PUBLICATION_FILES.json').read_bytes())
 assert set(selection)==set(result['modules'])==set(footers)
 assert footers==result['owned_export_counts']==final['environment_owned_export_counts']
 assert dict(collections.Counter(d['module']for d in public))==result['public_export_counts']==final['environment_public_export_counts']
 expected_total,expected_public=(179,112)
 assert len(owned)==result['total_owned_exports']==final['total_owned_exports']==expected_total
 assert len(public)==result['total_public_exports']==final['total_public_exports']==expected_public
 assert sha_file(R/'VALIDATION_RESULTS.json')['sha256']==final['validation_results_sha256']
 assert sha_file(R/'PUBLICATION_FILES.json')['sha256']==final['publication_files_sha256']
 assert len({x['path']for x in pubmanifest['files']})==len(pubmanifest['files'])
 for item in pubmanifest['files']:
  rel=Path(item['path']);assert not rel.is_absolute()and '..'not in rel.parts
  x=sha_file(R/rel);assert(x['bytes'],x['sha256'])==(item['bytes'],item['sha256']),('publication mismatch',item,x)
 print('batch',batch,'publication exact',len(pubmanifest['files']),flush=True)
 current={};mains={}
 for module,expected_sha in result['modules'].items():
  short=module.split('.')[-1];stage=result['source_plus_five_outputs'][module]
  assert len(stage)==6
  assert json.loads((R/(short+'-AFTER_NORMAL.json')).read_bytes())==json.loads((R/(short+'-AFTER_KERNEL.json')).read_bytes())==stage
  current[module]=[]
  for relative,expected in stage.items():
   item=sha_file(P/relative);assert(item['bytes'],item['sha256'])==(expected['bytes'],expected['sha256']),('current facet mismatch',module,item,expected)
   current[module].append(item)
  source_rel=module.replace('.','/')+'.lean'
  assert stage[source_rel]['sha256']==expected_sha==selection[module]['postimage_sha256']
  assert sha_file(R/short/'candidate.lean')['sha256']==expected_sha
  baseline=sha_file(R/short/'baseline.lean');assert baseline['sha256']==selection[module]['preimage_sha256']
  main=Path('/workspace/goldbach-formalization')/source_rel;published=final['actual_source_readback'][module]
  assert main.exists()==published['main_exists']
  mains[module]=sha_file(main)if main.exists()else None
  if main.exists():assert mains[module]['sha256']==published['main_source_sha256']==expected_sha
 commands=result['normal_commands']+result['kernel_commands']+[result['audit_command']]
 assert len(result['normal_commands'])==len(result['kernel_commands'])==len(result['modules'])
 for cmd in commands:
  assert cmd['exit_code']==0
  assert sha_file(R/cmd['log'])['sha256']==cmd['log_sha256']
  name='all-public-types-axioms-command.json'if cmd['name']=='all-public-types-axioms'else cmd['name']+'-command.json'
  assert json.loads((R/name).read_bytes())==cmd
  assert cmd['cwd']==str(P)
  assert cmd['argv'][cmd['argv'].index('--state')+1]=='/workspace/blue-build-tools/runtime-evidence/state.json'
 driver=(R/'PublicAudit.lean').read_text()
 assert 'set_option pp.all true'in driver and 'set_option pp.universes true'in driver
 assert 'getModuleIdxFor?'in driver and 'env.constants.fold'in driver
 assert 'reprStr info.type'in driver and 'info.levelParams'in driver and 'collectAxioms name'in driver
 assert 'info.isUnsafe'in driver and 'info.isAxiom'in driver
 assert sha_file(R/'PublicAudit.lean')['sha256']==json.loads((R/'AUDIT_SCOPE.json').read_bytes())['new_driver_sha256']
 runtime=json.loads((R/'ACTUAL_RUNTIME_COMMANDS.json').read_bytes())
 assert sha_file(runtime['state'])['sha256']==runtime['state_sha256']
 state=json.loads(Path(runtime['state']).read_bytes());events=runtime['actual_compiler_commands'];wanted={x['pid']:x for x in events.values()};found={}
 assert len(wanted)==len(result['modules'])+1
 with Path(state['log']).open('rb')as f:
  for line in f:
   d=json.loads(line)
   if d.get('pid')in wanted:assert d==wanted[d['pid']];found[d['pid']]=True
 assert set(found)==set(wanted)
 for e in events.values():
  assert e['cwd']==str(P)and all(x in e['command']for x in ['-t0','-j2','-M12288','maxRecDepth=100000','maxHeartbeats=4000000'])
  assert e['slot_owner']==str(e['pid'])
 static_reviews=[]
 for item in pubmanifest['files']:
  rel=item['path']
  if ('REVIEW' in Path(rel).name and 'MANIFEST'not in Path(rel).name and rel.endswith('.json')):
   v=json.loads((R/rel).read_bytes());assert not v.get('findings',[]),('prior static findings',rel,v.get('findings'))
   static_reviews.append({'path':rel,'sha256':item['sha256'],'reviewer':v.get('reviewer'),'source_author':v.get('author',v.get('candidate_author')),'status':v.get('status',v.get('result',v.get('outcome')))})
 out={'batch':batch,'original_publication_manifest':sha_file(R/'PUBLICATION_FILES.json'),'original_result':sha_file(R/'VALIDATION_RESULTS.json'),'original_final':sha_file(R/'FINAL_RELEASE.json'),'original_source_selection':sha_file(R/'SOURCE_SELECTION.json'),
  'all_original_publication_records_exact':len(pubmanifest['files']),'all_verified_records':cache,'current_source_plus_five':current,'main_readback':mains,'commands':commands,
  'owned_summary':{'owned':len(owned),'public':len(public),'private':sum(d['is_private']for d in owned),'owned_by_module':footers,'public_by_module':dict(collections.Counter(d['module']for d in public)),
  'kind_counts':dict(collections.Counter(d['kind']for d in owned)),'universe_nonempty':sum(bool(d['universe_parameters'])for d in owned),'observed_axiom_sets':[list(x)for x in sorted(set(tuple(sorted(d['axioms']))for d in owned))],
  'raw_exact_owned':True,'public_exact_nonprivate_subset':True,'name_inventory_exact':True,'full_original_and_decoded_type_and_AST_no_elision':True,'source_command_counts_not_used_as_environment_export_counts':True,'field_summaries':owned},
  'static_reviews':static_reviews,'actual_runtime_events_match_existing_original_journal':True,'no_new_Lean_Lake_kernel_audit_stock_source_or_controller_calls':True}
 outpath.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
 print('batch',batch,'DONE owned',len(owned),'public',len(public),'private',len(owned)-len(public),flush=True)
