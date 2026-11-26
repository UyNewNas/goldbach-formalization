from pathlib import Path
from collections import Counter,defaultdict
import ast,json,hashlib,sys,time,resource,datetime
start=time.monotonic();base=Path('p29-current');out=base/'nonunit-p3-facet-delta';assert not out.exists();out.mkdir()
reader=base/'verify-nonunit002-complete-root.py';reader_bytes=reader.read_bytes()
assert len(reader_bytes)==24917 and hashlib.sha256(reader_bytes).hexdigest()=='07200ca08452f61d0185371215e8644742d17e88ac9273cf536ba180d961b6d9'
tree=ast.parse(reader_bytes);nodes=[n for n in tree.body if isinstance(n,(ast.ClassDef,ast.FunctionDef))and n.name in {'JsonStream','graph_events'}]
assert len(nodes)==2
ns={'json':json,'Path':Path};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(reader)+'::two-reader-definitions','exec'),ns)
graph_events=ns['graph_events']

def fingerprint(path):
 p=Path(path);before=p.stat();h=hashlib.sha256();git=hashlib.sha1(b'blob '+str(before.st_size).encode()+b'\0');size=0
 with p.open('rb')as f:
  while block:=f.read(1048576):h.update(block);git.update(block);size+=len(block)
 after=p.stat();stamp=lambda s:[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
 assert stamp(before)==stamp(after)and size==before.st_size
 return {'path':str(p.resolve()),'bytes':size,'sha256':h.hexdigest(),'git_blob':git.hexdigest(),'stat':stamp(after)}

p1path=Path('/dev/shm/p29-nonunit002-reception/complete/evidence/consumer-actual-imports-bindings.json')
p3path=base/'unit-tail-qualified/verification/borrowed-actual-imports-bindings.json'
rootfile=base/'NONUNIT002_ROOT_ACCEPTANCE.json';root_acceptance=json.loads(rootfile.read_text());rootpin=fingerprint(rootfile)
assert rootpin['git_blob']=='36b6d39a60e2e64f68e6415ec8c8505a5f03d5b2'
supplyfile=base/'unit-tail-qualified/verification/SUPPLY_QUALIFICATION.json';supply=json.loads(supplyfile.read_text());supplypin=fingerprint(supplyfile)
assert supplypin['sha256']=='1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21'
assert supply['status']=='PASS_CURRENT_P3_BOUND_IMPORTS_NAMED_KERNEL_FULL_OWNED'
assert len(supply['borrowed_modules'])==18
pins={'P1':fingerprint(p1path),'P3':fingerprint(p3path)}
assert pins['P1']['sha256']==root_acceptance['actual_import_bindings_sha256']=='e3b54d774492b4b331d7f3c5bdfcdacd8d13983593e45e7d22aee1804b495e83'
assert pins['P3']['sha256']==supply['actual_import_bindings_sha256']=='6b0e29d00cf57429278bb0416c62f8642c15738a80c61bd4e0dd0b31513c2659'

# Stream the two fixed graph files; retain only headers and minimal identities.
def read_index(path,expected_roots):
 headers={};parts={};meta={}
 for key,value in graph_events(path):
  if key=='actual_modules':
   module=sys.intern(value['module']);assert module not in headers
   headers[module]=tuple(sys.intern(s)for s in value['direct_imports'])
  elif key=='parts':
   k=(sys.intern(value['module']),sys.intern(value['facet']));assert k not in parts
   identity=value['identity'];assert isinstance(identity['bytes'],int)and identity['bytes']>=0
   assert isinstance(identity['sha256'],str)and len(identity['sha256'])==64
   parts[k]=(identity['path'],identity['bytes'],identity['sha256'])
  else:meta[key]=value
 assert set(meta['roots'])==set(expected_roots)
 assert len(headers)==meta['module_count']and len(parts)==meta['part_count']
 assert {m for m,f in parts}==set(headers)
 assert all((m,'.olean')in parts for m in headers)
 reachable=set();todo=list(expected_roots)
 while todo:
  m=todo.pop()
  if m in reachable:continue
  assert m in headers,('Missing original header',m)
  reachable.add(m);todo.extend(headers[m])
 assert reachable<=set(headers)
 return meta,headers,parts,reachable

p1root='ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient'
p1meta,p1headers,p1parts,p1reachable=read_index(p1path,[p1root])
p3meta,p3headers,p3parts,p3reachable=read_index(p3path,supply['borrowed_modules'])
assert p1meta['module_count']==6185 and p1meta['part_count']==30821
assert p3meta['part_count']==21278
assert p1reachable==set(p1headers), 'The fixed Nonunit graph must be exactly its original root closure.'
assert p3reachable==set(p3headers), 'The fixed P3 graph must be exactly its accepted 18-root closure.'
counts=Counter();facet_counts=defaultdict(Counter);modules=defaultdict(set);module_categories=defaultdict(set);project_rows=[];header_differences=[]
paths={name:out/(name+'.jsonl')for name in ['same_bytes','same_key_different_bytes','only_P1_reachable']}
writers={name:p.open('x',encoding='utf-8')for name,p in paths.items()}

def ident(value):return {'path':value[0],'bytes':value[1],'sha256':value[2]}
try:
 for key in sorted(p1parts):
  module,facet=key
  if module not in p1reachable:continue
  left=p1parts[key];right=p3parts.get(key)
  if right is None:kind='only_P1_reachable'
  elif left[1:]==right[1:]:kind='same_bytes'
  else:kind='same_key_different_bytes'
  row={'module':module,'facet':facet,'P1':ident(left)}
  if right is not None:row['P3']=ident(right)
  if kind=='same_bytes':row['same_path']=left[0]==right[0]
  if kind=='same_key_different_bytes':row['different_fields']=[field for index,field in [(1,'bytes'),(2,'sha256')]if left[index]!=right[index]]
  writers[kind].write(json.dumps(row,ensure_ascii=False,separators=(',',':'))+'\n')
  counts[kind]+=1;facet_counts[kind][facet]+=1;modules[kind].add(module);module_categories[module].add(kind)
  if module.startswith('ImbalancedChen.'):project_rows.append({'classification':kind,**row})
 for module in sorted(p1reachable&set(p3headers)):
  if p1headers[module]!=p3headers[module]:header_differences.append({'module':module,'P1_direct_imports':p1headers[module],'P3_direct_imports':p3headers[module]})
finally:
 for f in writers.values():f.close()
assert sum(counts.values())==len(p1parts)==30821
assert set(module_categories)==p1reachable
# A header difference is reported, not silently reclassified as a byte conflict.
(out/'overlap_header_differences.json').write_text(json.dumps(header_differences,ensure_ascii=False,indent=2)+'\n')
file_pins={name:fingerprint(p)for name,p in paths.items()}
for name,path in [('P1',p1path),('P3',p3path)]:
 s=path.stat();assert [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]==pins[name]['stat']
summary={
 'schema':'p29_nonunit_root_to_accepted_P3_supply_exact_facet_comparison_v1',
 'status':'COMPLETE_LOCAL_BYTES_COMPARISON_ONLY',
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Only the exact original Nonunit root-reachable inputs, compared against the existing accepted Unit P3 18-supplier graph.',
 'P1':{'graph':pins['P1'],'original_root_acceptance':rootpin,'root_acceptance_commit':'952caa6e5bb055bb5a4ed87d1d9855de36e4b35a','roots':p1meta['roots'],'modules':len(p1reachable),'facets':len(p1parts)},
 'P3':{'graph':pins['P3'],'original_supply_qualification':supplypin,'roots':p3meta['roots'],'modules':len(p3reachable),'facets':len(p3parts),'consumer_graph_5edc780b_not_used_or_mixed':True},
 'comparison_key':['module','facet'],
 'byte_equality_fields':['identity.bytes','identity.sha256'],
 'paths_ignored_for_byte_equality':True,
 'counts':{name:counts[name]for name in paths},
 'distinct_modules_per_category':{name:len(modules[name])for name in paths},
 'module_category_combination_counts':dict(sorted(Counter('+'.join(sorted(v))for v in module_categories.values()).items())),
 'facet_counts':{name:dict(sorted(facet_counts[name].items()))for name in paths},
 'exact_lists':file_pins,
 'project_module_rows':project_rows,
 'overlap_header_difference_count':len(header_differences),
 'overlap_header_differences_file':fingerprint(out/'overlap_header_differences.json'),
 'reader_reuse':{'file':str(reader.resolve()),'bytes':len(reader_bytes),'sha256':hashlib.sha256(reader_bytes).hexdigest(),'definitions':['JsonStream','graph_events'],'definitions_extracted_unchanged_by_AST':True,'original_verifier_top_level_executed':False},
 'existing_work_check':{'no_complete_existing_comparison_found_in_local_related_report_inventory':True,'profile_confirmed_only_project_projection_and_Power_name_lookup_preexisted':True,'existing_project_projection':'p29-atlas-1126/OMITTED_SELECTIVE_58_PROJECT_SUPPLIER_PROJECTION.json'},
 'interpretation':{'same_bytes':'Exact prior P3 facet bytes are available in the accepted snapshot and are candidates for reuse at the recorded P3 path. Current remote existence/stat is not freshly checked here.','same_key_different_bytes':'Identical module/facet key has different byte count or SHA; do not merge these inputs merely because module/source names agree. No substitution was made.','only_P1_reachable':'No matching module/facet key is in the selected accepted P3 graph. The exact original P1 path and required bytes/SHA are listed. This is not a claim of absence everywhere on P3.'},
 'work_performed':{'streamed_large_JSON_files':2,'large_JSON_json_load_calls':0,'large_graph_copies':0,'old_owned_rechecks':0,'Lean_processes':0,'remote_calls':0,'export_jobs':0,'new_controller':False,'new_proof_credit':0,'elapsed_seconds':round(time.monotonic()-start,3),'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},
 'P3_full_native_reception_or_Omitted_qualification_established':False
}
p=out/'SUMMARY.json';p.write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'summary':str(p.resolve()),'counts':summary['counts'],'distinct_modules_per_category':summary['distinct_modules_per_category'],'module_category_combination_counts':summary['module_category_combination_counts'],'overlap_header_difference_count':len(header_differences),'exact_list_files':file_pins,'project_module_rows':project_rows,'elapsed_seconds':summary['work_performed']['elapsed_seconds'],'peak_RSS_KiB':summary['work_performed']['peak_RSS_KiB']},ensure_ascii=False))
