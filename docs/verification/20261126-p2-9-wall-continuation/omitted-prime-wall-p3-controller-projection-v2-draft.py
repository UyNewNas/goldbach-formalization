import pathlib,os,sys,json,hashlib,subprocess,time,signal,datetime,traceback,shutil,tomllib,importlib.util,urllib.request,base64,re,tarfile
P=pathlib.Path
sys.dont_write_bytecode=True

# DRAFT: this intentionally unset SHA blocks before any directory write,
# source fetch, receiver qualification or Lean process.
CONTRACT_SHA256=None
contract_text=globals().get('INPUT_CONTRACT_TEXT')
assert isinstance(CONTRACT_SHA256,str)and len(CONTRACT_SHA256)==64,'Pending exact supplier contract; do not run this draft.'
assert isinstance(contract_text,str)and hashlib.sha256(contract_text.encode()).hexdigest()==CONTRACT_SHA256
contract=json.loads(contract_text)
assert contract['schema']=='p29_omitted_single_target_input_contract_v2'
assert contract['status']=='ROOT_ACCEPTED_READY_FOR_ONE_TARGET'and contract['pending_requirements']==[]
assert contract['receiver_root']=='/workspace/p29-omitted-prime-wall-20261126-ef40c77'
assert contract['target']=={'module': 'ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall', 'source_git_blob': 'ef40c77ee9b4c58a8e4761b21fafdfe867f85d8e', 'source_sha256': '4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c', 'source_bytes': 7887, 'direct_imports': ['ImbalancedChen.AffinePrimeWallReserve', 'ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient', 'ImbalancedChen.P2MarkedPrimeProductFibreCore', 'Mathlib.Algebra.BigOperators.Fin', 'Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset']}
assert set(contract['authorities'])=={'nonunit','affine_poly'}
assert contract['new_supplier_replays']==contract['existing_Unit_Gate_replays']==contract['new_proof_credit']==0
assert contract['combined_actual_import_probe_already_run']is False
contract_files={}
for key,authority in contract['authorities'].items():
 assert authority['status']=='ROOT_ACCEPTED_EXACT_ORIGINAL_PROOF_AND_P3_BYTES'
 archive=authority['original_complete_archive']
 assert isinstance(archive,dict)and re.fullmatch('[0-9a-f]{64}',archive['sha256'])and archive['bytes']>0
 assert isinstance(archive['parts'],list)and archive['parts']
 offset=0
 for index,p in enumerate(archive['parts']):
  assert p['index']==index and p['offset']==offset and isinstance(p['bytes'],int)and p['bytes']>0
  assert re.fullmatch('[0-9a-f]{40}',p['git_blob'])and re.fullmatch('[0-9a-f]{64}',p['sha256']);offset+=p['bytes']
 assert offset==archive['bytes']
 assert authority['source_compilations_in_this_run']==authority['kernel_owned_replays_in_this_run']==0
 assert set(authority['expected_root_objects'])==set(authority['qualified_roots'])
 for mod,expected in authority['expected_root_objects'].items():
  assert set(expected)=={'source_sha256','object_sha256'}
  assert all(isinstance(h,str)and re.fullmatch('[0-9a-f]{64}',h)for h in expected.values())
 labels=['root_acceptance','qualification_receipt','original_actual_bindings','relocation_binding','normalized_project_objects','normalized_actual_inputs']
 labels+=['original_source_outputs','original_manifest','original_archive_index']if key=='nonunit'else['original_normal_records','original_external_snapshot']
 assert isinstance(authority['selected_project_modules'],list)and authority['selected_project_modules']
 assert isinstance(authority['expected_owned_counts'],dict)and set(authority['expected_owned_counts'])==set(authority['qualified_roots'])
 assert all(isinstance(n,int)and n>0 for n in authority['expected_owned_counts'].values())
 if key=='affine_poly':assert isinstance(authority['original_field_bindings'],dict)and authority['original_field_bindings']
 for label in labels:
  rec=authority[label];assert isinstance(rec,dict)and set(rec)=={'path','bytes','sha256'}
  p=P(rec['path']);assert p.is_absolute()and p.is_relative_to('/workspace')and not p.is_relative_to(contract['receiver_root'])
  assert isinstance(rec['bytes'],int)and rec['bytes']>0 and re.fullmatch('[0-9a-f]{64}',rec['sha256'])
  st=p.stat();before=[st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns];digest=hashlib.sha256();size=0
  with p.open('rb')as f:
   while block:=f.read(1024*1024):digest.update(block);size+=len(block)
  st=p.stat();assert before==[st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns]
  assert size==rec['bytes']and digest.hexdigest()==rec['sha256']
  if str(p)in contract_files:assert contract_files[str(p)]=={'record':rec,'stat':before}
  contract_files[str(p)]={'record':rec,'stat':before}
assert isinstance(contract['expected_merged_project_modules'],list)and contract['expected_merged_project_modules']
assert isinstance(contract['permitted_research_modules'],list)
assert isinstance(contract['expected_merged_actual_module_count'],int)and contract['expected_merged_actual_module_count']>0
assert isinstance(contract['expected_merged_part_count'],int)and contract['expected_merged_part_count']>0
assert re.fullmatch('[0-9a-f]{64}',contract['expected_merged_part_map_sha256'])

projection_record=contract['project_projection'];projection_path=P(projection_record['path'])
assert projection_path.is_absolute()and projection_path.is_relative_to('/workspace')and not projection_path.is_relative_to(contract['receiver_root'])
st=projection_path.stat();projection_stat=[st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns]
projection_raw=projection_path.read_bytes();st=projection_path.stat()
assert projection_stat==[st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns]
assert len(projection_raw)==51530==projection_record['bytes']
assert hashlib.sha256(projection_raw).hexdigest()==projection_record['sha256']=='6e17baca207d13c563770fd5f2303bef05bb00488e47cb120e02eb31949fc55f'
assert hashlib.sha1(b'blob '+str(len(projection_raw)).encode()+b'\0'+projection_raw).hexdigest()=='b7e2341c1d33145e65319b2bf99b375f8bb81715'
project_projection=json.loads(projection_raw)
assert project_projection['target']==contract['target']['module']and project_projection['target_source_blob']==contract['target']['source_git_blob']
assert len(project_projection['selected_modules'])==58==contract['expected_merged_project_module_count']
assert sorted(project_projection['selected_modules'])==contract['expected_merged_project_modules']
assert contract['after_target_project_module_count']==59 and contract['P2_P3_Power_objects_declared_equal']is False
contract_files[str(projection_path)]={'record':projection_record,'stat':projection_stat}
capacity=contract['capacity_budget'];assert capacity['status']=='ROOT_REVIEWED_MEASURED_NEW_OUTPUT_BUDGET'
assert capacity['host']=='P3'and capacity['destination_filesystem']=='/workspace'and capacity['alternate_output_filesystem_or_host_selected']is False
assert isinstance(capacity['source_of_measurement'],dict)and capacity['source_of_measurement']
assert isinstance(capacity['components_bytes'],dict)and set(capacity['components_bytes'])=={'raw_import_logs','actual_binding_graphs','target_outputs','audit_and_control_evidence','final_archive','filesystem_overhead'}
assert all(isinstance(n,int)and n>0 for n in capacity['components_bytes'].values())
assert sum(capacity['components_bytes'].values())==capacity['peak_new_output_bytes']
assert isinstance(capacity['minimum_remaining_free_bytes'],int)and capacity['minimum_remaining_free_bytes']>0
assert isinstance(capacity['required_available_memory_bytes'],int)and capacity['required_available_memory_bytes']>0
disk=shutil.disk_usage('/workspace');meminfo=dict((k,int(v.split()[0])*1024)for k,v in(line.split(':',1)for line in P('/proc/meminfo').read_text().splitlines()))
capacity_initial={'workspace_free_bytes':disk.free,'MemAvailable_bytes':meminfo['MemAvailable'],'required_new_output_budget_bytes':capacity['peak_new_output_bytes'],'minimum_remaining_free_bytes':capacity['minimum_remaining_free_bytes'],'required_available_memory_bytes':capacity['required_available_memory_bytes']}
assert disk.free>=capacity['peak_new_output_bytes']+capacity['minimum_remaining_free_bytes'],'Insufficient measured space; do not create or run the target.'
assert meminfo['MemAvailable']>=capacity['required_available_memory_bytes'],'Insufficient measured memory; do not create or run the target.'

base=P('/workspace/p29-omitted-prime-wall-20261126-ef40c77')
oldbase=P('/workspace/p29-unit-tail-20261126-8131f7d6')
oldout=oldbase/'verification'
root=base/'project';out=base/'verification'
assert not base.exists(),'Do not repeat this independent Omitted receiver; read its existing receipt first.'
base.mkdir();root.mkdir();out.mkdir()
(out/'driver.py').write_text(SOURCE_TEXT)
(out/'INPUT_CONTRACT.json').write_text(contract_text)
(out/'CAPACITY_BEFORE_NEW_WRITES.json').write_text(json.dumps(capacity_initial,indent=2)+'\n')
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
target='ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall'
source_blob='ef40c77ee9b4c58a8e4761b21fafdfe867f85d8e'
source_sha='4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c'
source=get_blob(source_blob)
assert len(source)==7887 and hashlib.sha256(source).hexdigest()==source_sha
source_imports=re.findall(r'^import\s+(\S+)',source.decode(),re.M)
assert source_imports==contract['target']['direct_imports']
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

# The old qualification remains an18-module immutable authority. Only the
# exact header-reachable FibreCore/explicit-Mathlib branch enters this target.
def reachable_headers(roots,rows):
 seen=set();pending=list(roots)
 while pending:
  mod=pending.pop()
  if mod in seen:continue
  assert mod in rows,('Missing original module header',mod)
  seen.add(mod);pending.extend(rows[mod]['direct_imports'])
 return seen

original_P3_qualified_input_count=old_inputs['part_count']
assert original_P3_qualified_input_count==21278
original_P3_rows={row['module']:row for row in old_inputs['actual_modules']}
assert len(original_P3_rows)==len(old_inputs['actual_modules'])==old_inputs['module_count']
P3_selected_roots=contract['base_P3_qualification']['selected_import_roots']
assert P3_selected_roots==['ImbalancedChen.P2MarkedPrimeProductFibreCore',*source_imports[3:]]
P3_selected_modules=reachable_headers(P3_selected_roots,original_P3_rows)
assert {m for m in P3_selected_modules if m.startswith('ImbalancedChen.')}==set(contract['base_P3_qualification']['selected_project_modules'])=={'ImbalancedChen.P2MarkedPrimeProductFibreCore'}
P3_selected_parts=[part for part in old_inputs['parts']if part['module']in P3_selected_modules]
old_inputs={'roots':P3_selected_roots,'module_count':len(P3_selected_modules),'part_count':len(P3_selected_parts),'actual_modules':[original_P3_rows[m]for m in sorted(P3_selected_modules)],'parts':P3_selected_parts}
save(out/'ORIGINAL_P3_SELECTED_HEADER_PROJECTION.json',{'schema':'p29_omitted_existing_P3_header_subset_v1','original_graph_sha256':old_receipts['borrowed-actual-imports-bindings.json'],'original_qualified_parts':original_P3_qualified_input_count,'original_qualified_project_modules':18,'selected_roots':P3_selected_roots,'selected_project_modules':contract['base_P3_qualification']['selected_project_modules'],'selected_modules':sorted(P3_selected_modules),'selected_parts':len(P3_selected_parts),'old_qualification_unchanged':True,'old_normal_kernel_owned_replays':0})

old_by_part={}
for i,part in enumerate(old_inputs['parts']):
 p=P(part['identity']['path']);expected=part['identity'];s=part['stat_snapshot']
 assert stamp(p)==s and p.stat().st_size==expected['bytes'] and sha(p)==expected['sha256'],('Old qualified input changed',str(p))
 assert stamp(p)==s;cache_before[str(p)]=s
 key=(part['module'],part['facet']);assert key not in old_by_part;old_by_part[key]=part
 if i%4000==0:print(json.dumps({'stage':'old-qualified-input-byte-stability','checked_parts':i,'total':len(old_inputs['parts']),'new_proof_credit':0}),flush=True)
assert len(old_by_part)==old_inputs['part_count']==len(P3_selected_parts)

# Data projections retain the exact original evidence and current P3 paths.
# Missing qualifications cannot be manufactured by this controller.
for path,bound in contract_files.items():
 assert stamp(path)==bound['stat'];preserve(path,bound['record']['sha256'])
base_old_inputs=old_inputs
base_old_by_part=dict(old_by_part)
combined_borrows={m:old_borrows[m]for m in contract['base_P3_qualification']['selected_project_modules']}
combined_rows={row['module']:row for row in old_inputs['actual_modules']}
qualified_research=set(contract['permitted_research_modules'])

# Exact original receipts are parsed below. Normalized handoffs cannot by
# themselves create qualification or substitute for an original acceptance.
def original_field(document,pointer):
 assert isinstance(pointer,list)and pointer
 value=document
 for key in pointer:
  assert isinstance(key,(str,int))
  value=value[key]
 return value

def bind_original_nonunit(authority,original_inputs,original_parts):
 nt='ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient'
 raw=P(authority['root_acceptance']['path']).read_bytes()
 assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='36b6d39a60e2e64f68e6415ec8c8505a5f03d5b2'
 accepted=json.loads(raw)
 assert accepted['schema']=='p29_nonunit002_root_acceptance_v1'
 assert accepted['status']=='ROOT_ACCEPTED_EXACT_NORMAL_KERNEL_FULL_OWNED_AND_COMPLETE_81_MEMBER_ARCHIVE'
 assert accepted['module']==nt and accepted['aggregate_exit_code']==0
 assert authority['root_acceptance_origin']=={'commit':'952caa6e5bb055bb5a4ed87d1d9855de36e4b35a','path':'docs/verification/20261126-p2-9-nonunit-quotient/ROOT_ACCEPTANCE.json','git_blob':'36b6d39a60e2e64f68e6415ec8c8505a5f03d5b2'}
 assert accepted['source_blob']=='eeaf7a2c714da44928cc43e79780846e1e72d23b'
 assert accepted['source_sha256']==authority['expected_root_objects'][nt]['source_sha256']=='42de161d084cac904775203fb0188bcc7bc5459a9b230b53c5c405e692262d77'
 assert accepted['object_blob']=='be40b1d4d962e849be5018a7d8b22241d699818d'
 assert accepted['object_sha256']==authority['expected_root_objects'][nt]['object_sha256']=='86ade819d9ae33358ea6ea00b419c4ddfb6727b28637145c45b1ca412a849eb8'
 assert accepted['object_bytes']==authority['expected_target_object_bytes']==210800
 assert accepted['validation_sha256']==authority['qualification_receipt']['sha256']=='b818e145c7356d3ce8a5d0e34b887058996ba6a86e9010900ff19536fe83f170'
 assert accepted['actual_import_bindings_sha256']==authority['original_actual_bindings']['sha256']=='e3b54d774492b4b331d7f3c5bdfcdacd8d13983593e45e7d22aee1804b495e83'
 assert accepted['manifest_sha256']==authority['original_manifest']['sha256']=='9a0cf3eae96fb78bd63d46e4b9df6e68346c03ecaea50a498020ae11675e9de9'
 assert authority['original_file_member_keys']=={'qualification_receipt':'evidence/VALIDATION_RESULTS.json','original_source_outputs':'evidence/SOURCE_AND_OUTPUTS_AFTER.json','original_actual_bindings':'evidence/consumer-actual-imports-bindings.json'}
 assert authority['original_source_outputs']['sha256']=='7e11d3b1fde9b0940e11a65328f8aeec1c2a431600cb7fa0b950fd02e15f47d7'
 manifest=json.loads(P(authority['original_manifest']['path']).read_text());assert len(manifest)==80
 for label,member in authority['original_file_member_keys'].items():
  assert manifest[member]=={k:authority[label][k]for k in ['bytes','sha256']}
 index_raw=P(authority['original_archive_index']['path']).read_bytes()
 assert hashlib.sha1(b'blob '+str(len(index_raw)).encode()+b'\0'+index_raw).hexdigest()==accepted['archive_parts_index_blob']=='3f6ea77f9a707055b54fa8f8b18e7eee165e2e48'
 index=json.loads(index_raw);archive=authority['original_complete_archive']
 assert index['archive_sha256']==archive['sha256']==accepted['archive_sha256']=='9db6e95658f7be4377b04f5affa0687df88dce03552863389d8696c6d24641bc'
 assert index['archive_bytes']==archive['bytes']==accepted['archive_bytes']==7419000
 assert [{k:r[k]for k in ['index','offset','bytes','sha256','git_blob']}for r in index['parts']]==archive['parts']
 assert index['members']==archive['members']==accepted['archive_members']==81
 receipt=json.loads(P(authority['qualification_receipt']['path']).read_text())
 assert receipt['result']=='PASS_ONE_NEW_NONUNIT_QUOTIENT_NORMAL_STOCK_NAMED_KERNEL_FULL_OWNED'
 assert receipt['modules']==[nt]
 assert receipt['inputs']==[{'module':nt,'blob':accepted['source_blob'],'bytes':3431,'sha256':accepted['source_sha256']}]
 assert receipt['owned_declaration_counts']==authority['expected_owned_counts']=={nt:17}and accepted['owned']==17
 assert receipt['normal']['exit_code']==receipt['kernel']['exit_code']==receipt['owned']['exit_code']==0
 assert accepted['normal_exit']==accepted['named_kernel_exit']==accepted['full_owned_exit']==0
 assert receipt['normal_warning_as_error_requested']is accepted['normal_warningAsError']is False
 assert receipt['normal_warning_count']==accepted['normal_warning_count']==3
 assert receipt['actual_import_bindings_sha256']==accepted['actual_import_bindings_sha256']
 assert receipt['before_actual_import_bindings_sha256']==receipt['reused_union_bindings_sha256']=='74a28fe0612de36a7d4df66f78af7ad5207288ec2cdf7054fc2112e75b597c69'
 assert receipt['source_and_outputs_unchanged_after_normal']is True
 assert receipt['old_source_recompilations']==receipt['old_kernel_replays']==receipt['old_owned_replays']==receipt['old_supplier_new_formal_credit']==0
 assert receipt['supplier_import_probe_repeated']is receipt['guard_setup_repeated']is False
 assert receipt['observed_axioms']==accepted['axioms']==['Classical.choice','Quot.sound','propext']
 assert accepted['full_p2_9_complete']is accepted['board_node_promoted']is False
 outputs=json.loads(P(authority['original_source_outputs']['path']).read_text())
 production_root=authority['original_production_root'];assert production_root=='/workspace/p29-nonunit-quotient-20261126-0117dd4'
 source_path=production_root+'/'+nt.replace('.','/')+'.lean'
 object_path=production_root+'/.lake/build/lib/lean/'+nt.replace('.','/')+'.olean'
 assert outputs[source_path]=={'bytes':3431,'sha256':accepted['source_sha256']}
 assert outputs[object_path]=={'bytes':210800,'sha256':accepted['object_sha256']}
 assert original_parts[(nt,'.olean')]['identity']=={'path':object_path,**outputs[object_path]}
 assert original_inputs['module_count']==authority['expected_original_module_count']==accepted['after_actual_imports']['modules']==6185
 assert original_inputs['part_count']==authority['expected_original_part_count']==accepted['after_actual_imports']['facets']==30821
 assert original_inputs['roots']==[nt]
 return {'root_acceptance_blob':'36b6d39a60e2e64f68e6415ec8c8505a5f03d5b2','target':nt,'source_sha256':accepted['source_sha256'],'object_sha256':accepted['object_sha256'],'validation_sha256':accepted['validation_sha256'],'actual_graph_sha256':accepted['actual_import_bindings_sha256'],'source_outputs_sha256':authority['original_source_outputs']['sha256'],'manifest_sha256':accepted['manifest_sha256'],'parsed_original_owned_count':17,'normal_warning_as_error':False,'normal_warning_count':3,'new_proof_credit':0}

def bind_original_affine(authority):
 labels=['root_acceptance','qualification_receipt','original_normal_records']
 documents={label:json.loads(P(authority[label]['path']).read_text())for label in labels}
 assert authority['original_external_snapshot']['sha256']==authority['original_native_snapshot_sha256']=='ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
 bindings=authority['original_field_bindings'];expected={
  'root_validation_sha256':('root_acceptance',authority['qualification_receipt']['sha256']),
  'root_actual_graph_sha256':('root_acceptance',authority['original_actual_bindings']['sha256']),
  'root_external_snapshot_sha256':('root_acceptance',authority['original_external_snapshot']['sha256']),
 }
 for mod,pin in authority['expected_root_objects'].items():
  for field in ['source_sha256','object_sha256']:
   expected[mod+':root_'+field]=('root_acceptance',pin[field])
   expected[mod+':normal_'+field]=('original_normal_records',pin[field])
  expected[mod+':normal_exit']=('original_normal_records',0)
  expected[mod+':kernel_exit']=('qualification_receipt',0)
  expected[mod+':owned_exit']=('qualification_receipt',0)
  expected[mod+':owned_count']=('qualification_receipt',authority['expected_owned_counts'][mod])
 assert set(bindings)==set(expected)
 for role,(label,value)in expected.items():
  binding=bindings[role];assert set(binding)=={'file','pointer'}and binding['file']==label
  assert original_field(documents[label],binding['pointer'])==value,('Original Affine authority field mismatch',role)
 return {'original_fields_checked':sorted(expected),'root_acceptance_sha256':authority['root_acceptance']['sha256'],'original_validation_sha256':authority['qualification_receipt']['sha256'],'original_actual_graph_sha256':authority['original_actual_bindings']['sha256'],'original_external_snapshot_sha256':authority['original_external_snapshot']['sha256'],'target_owned_counts':authority['expected_owned_counts'],'new_proof_credit':0}

authority_summaries={}
for key,authority in contract['authorities'].items():
 objects=json.loads(P(authority['normalized_project_objects']['path']).read_text())
 inputs=json.loads(P(authority['normalized_actual_inputs']['path']).read_text())
 relocation=json.loads(P(authority['relocation_binding']['path']).read_text())
 original_inputs=json.loads(P(authority['original_actual_bindings']['path']).read_text())
 assert objects['schema']=='p29_received_project_object_map_v1'
 assert inputs['schema']=='p29_received_actual_input_bindings_v1'
 assert relocation['schema']=='p29_existing_proof_exact_byte_relocation_v1'
 assert relocation['old_normal_kernel_owned_replays']==relocation['new_proof_credit']==0
 for document in [objects,inputs]:
  assert document['root_acceptance_sha256']==authority['root_acceptance']['sha256']
  assert document['qualification_receipt_sha256']==authority['qualification_receipt']['sha256']
  assert document['relocation_binding_sha256']==authority['relocation_binding']['sha256']
 assert inputs['original_actual_bindings_sha256']==authority['original_actual_bindings']['sha256']
 assert set(inputs['roots'])==set(authority['qualified_roots'])
 assert set(inputs['roots'])<=set(objects['objects'])
 assert set(original_inputs['roots'])==set(inputs['roots'])
 original_parts={(part['module'],part['facet']):part for part in original_inputs['parts']}
 assert len(original_parts)==len(original_inputs['parts'])==original_inputs['part_count']
 original_rows={row['module']:row for row in original_inputs['actual_modules']}
 assert len(original_rows)==len(original_inputs['actual_modules'])==original_inputs['module_count']
 assert set(original_rows)==reachable_headers(inputs['roots'],original_rows)
 assert set(objects['objects'])=={m for m in original_rows if m.startswith('ImbalancedChen.')}==set(authority['selected_project_modules'])
 original_receipt_binding=bind_original_nonunit(authority,original_inputs,original_parts)if key=='nonunit'else bind_original_affine(authority)
 for mod in objects['objects']:
  assert mod in project_projection['selected_modules']
  pin=project_projection['selected_modules'][mod]
  assert objects['objects'][mod]['source_sha256']==pin['source_sha256']and objects['objects'][mod]['object_sha256']==pin['object_sha256']
  assert objects['objects'][mod]['direct_project_imports']==[m for m in original_rows[mod]['direct_imports']if m.startswith('ImbalancedChen.')]
  if isinstance(pin.get('direct_project_imports'),list):assert objects['objects'][mod]['direct_project_imports']==pin['direct_project_imports']
 assert len(inputs['parts'])==len({(part['module'],part['facet'])for part in inputs['parts']})
 assert set(original_parts)=={(part['module'],part['facet'])for part in inputs['parts']}
 assert len(inputs['actual_modules'])==len({row['module']for row in inputs['actual_modules']})
 assert set(original_rows)=={row['module']for row in inputs['actual_modules']}
 relocations={}
 for item in relocation['parts']:
  k=(item['module'],item['facet']);assert k not in relocations
  original=item['original_identity'];current=item['current_identity']
  assert k in original_parts and original==original_parts[k]['identity']
  assert original['bytes']==current['bytes']and original['sha256']==current['sha256']
  relocations[k]=current
 assert set(relocations)==set(original_parts)
 for mod,row in objects['objects'].items():
  assert row['module']==mod and mod.startswith('ImbalancedChen.')
  assert row['object_sha256']==original_parts[(mod,'.olean')]['identity']['sha256']
  assert row['object_bytes']==original_parts[(mod,'.olean')]['identity']['bytes']
  assert row['producer']['source_sha256']==row['source_sha256']
  assert row['producer']['object_sha256']==row['object_sha256']
  if mod in combined_borrows:
   prior=combined_borrows[mod]
   for field in ['source_sha256','source_bytes','object_sha256','object_bytes','direct_project_imports']:
    assert row[field]==prior[field],('Conflicting existing source/object authority',mod,field)
  else:combined_borrows[mod]=row
 for row in inputs['actual_modules']:
  mod=row['module']
  assert row['is_module']==original_rows[mod]['is_module']and row['direct_imports']==original_rows[mod]['direct_imports']
  if mod in combined_rows:
   prior=combined_rows[mod]
   assert row['is_module']==prior['is_module']and row['direct_imports']==prior['direct_imports'],('Conflicting module headers',mod)
  else:combined_rows[mod]=row
 for part in inputs['parts']:
  k=(part['module'],part['facet']);identity=part['identity'];p=P(identity['path'])
  assert k in relocations and relocations[k]==identity
  original_part=original_parts[k]
  assert part['authority']=='received_exact_prior_qualified_part'
  assert part['provider']=={'original_authority':original_part['authority'],'original_provider':original_part.get('provider',original_part.get('provider_binding',{})),'original_identity':original_part['identity'],'original_actual_bindings_sha256':authority['original_actual_bindings']['sha256']}
  assert p.is_absolute()and p.is_relative_to('/workspace')and not p.is_relative_to(base)
  assert p.resolve()==p and stamp(p)==part['stat_snapshot']and p.stat().st_size==identity['bytes']and sha(p)==identity['sha256']
  assert stamp(p)==part['stat_snapshot'];cache_before[str(p)]=part['stat_snapshot']
  if k in old_by_part:
   prior=old_by_part[k]
   assert identity==prior['identity']and part['stat_snapshot']==prior['stat_snapshot'],('Overlap needs the identical chosen P3 path/bytes',k)
  else:old_by_part[k]=part
 assert len(inputs['parts'])==inputs['part_count']and len(inputs['actual_modules'])==inputs['module_count']
 authority_summaries[key]={'original_complete_archive':authority['original_complete_archive'],'qualified_roots':authority['qualified_roots'],'root_acceptance':authority['root_acceptance'],'qualification_receipt':authority['qualification_receipt'],'original_actual_bindings':authority['original_actual_bindings'],'relocation_binding':authority['relocation_binding'],'normalized_project_objects':authority['normalized_project_objects'],'normalized_actual_inputs':authority['normalized_actual_inputs'],'original_receipt_field_binding':original_receipt_binding,'reused_project_modules':sorted(objects['objects']),'actual_modules':inputs['module_count'],'actual_parts':inputs['part_count'],'new_source_kernel_owned_replays':0}
assert set(combined_borrows)==set(contract['expected_merged_project_modules'])==set(project_projection['selected_modules'])
assert len(combined_borrows)==58
for mod,row in combined_borrows.items():
 pin=project_projection['selected_modules'][mod]
 assert row['source_sha256']==pin['source_sha256']and row['object_sha256']==pin['object_sha256']
assert combined_borrows['ImbalancedChen.PowerErrorBudget']['object_sha256']==contract['selected_P2_Power_object_sha256']=='3368b46534ec9238da4825e075bb7ba901b40fdaf8a203189ade30a6afcdf514'
assert old_borrows['ImbalancedChen.PowerErrorBudget']['object_sha256']==contract['base_P3_qualification']['unused_P3_Power_object_sha256']=='3463655903b309bfa3fdf3fcbc526a5ce6eb73eff1c1cde29bdaace7f300b9ec'
assert set(combined_rows)==reachable_headers(source_imports,combined_rows)
assert set(combined_borrows)=={m for m in combined_rows if m.startswith('ImbalancedChen.')}
assert target not in combined_borrows and target not in combined_rows,'The target already has a qualified object; do not recompile it.'
for authority in contract['authorities'].values():
 for mod,expected in authority['expected_root_objects'].items():
  assert combined_borrows[mod]['source_sha256']==expected['source_sha256']
  assert combined_borrows[mod]['object_sha256']==expected['object_sha256']
assert len(combined_rows)==contract['expected_merged_actual_module_count']
assert len(old_by_part)==contract['expected_merged_part_count']
canonical_part_map=[{'module':m,'facet':f,'identity':p['identity']}for(m,f),p in sorted(old_by_part.items())]
assert hashlib.sha256((json.dumps(canonical_part_map,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()==contract['expected_merged_part_map_sha256']
assert qualified_research=={m for m in combined_rows if m.startswith(('MathlibNt.','PrimeNumberTheoremAnd.','Architect.'))}
assert all(m in combined_rows for m,f in old_by_part)
old_inputs={'roots':source_imports,'actual_modules':[combined_rows[m]for m in sorted(combined_rows)],'parts':[old_by_part[k]for k in sorted(old_by_part)],'module_count':len(combined_rows),'part_count':len(old_by_part)}
save(out/'QUALIFIED_AUTHORITY_UNION.json',{'schema':'p29_omitted_prepared_authority_union_v1','input_contract_sha256':CONTRACT_SHA256,'original_P3_qualified_parts':original_P3_qualified_input_count,'selected_P3_parts':len(base_old_by_part),'total_modules':len(combined_rows),'total_parts':len(old_by_part),'canonical_part_map_sha256':contract['expected_merged_part_map_sha256'],'authorities':authority_summaries,'project_modules':sorted(combined_borrows),'explicit_research_modules':sorted(qualified_research),'actual_combined_import_probe_not_yet_run':True,'new_source_kernel_owned_replays':0,'new_proof_credit':0})

borrows={}
for mod,r in combined_borrows.items():
 assert set(r['direct_project_imports'])<=set(combined_borrows)
 for key in ['source','original_source']:
  assert preserve(r[key],r['source_sha256'])['bytes']==r['source_bytes']
 for key in ['object','original_object']:
  assert preserve(r[key],r['object_sha256'])['bytes']==r['object_bytes']
 assert re.findall(r'^import\s+(ImbalancedChen\.\S+)',P(r['source']).read_text(),re.M)==r['direct_project_imports']
 dest=lib/(mod.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(P(r['object']).resolve())
 new=dict(r);new['object']=str(dest);new['reused_qualified_object']=r['object'];new['new_source_compilation']=False;borrows[mod]=new

# Expose only newly admitted nonproject facets. Existing standard paths and
# every original source/object remain unchanged; no source is staged here.
extra_search_bindings=[]
for (mod,facet),part in sorted(old_by_part.items()):
 if mod.startswith('ImbalancedChen.')or(mod,facet)in base_old_by_part:continue
 assert facet in ['.olean','.olean.server','.olean.private','.ir.sig','.ir']
 original=P(part['identity']['path'])
 assert original.parts[-len(P(mod.replace('.','/')+facet).parts):]==P(mod.replace('.','/')+facet).parts
 dest=lib/(mod.replace('.','/')+facet)
 assert not dest.exists()and not dest.is_symlink()
 dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(original)
 extra_search_bindings.append({'module':mod,'facet':facet,'requested_path':str(dest),'resolved_identity':part['identity']})
save(out/'EXTRA_QUALIFIED_SEARCH_PATHS.json',{'schema':'p29_omitted_exact_received_nonproject_search_paths_v1','parts':extra_search_bindings,'new_source_compilations':0,'new_kernel_owned_replays':0,'original_provider_metadata_is_provenance_not_new_checkout_claim':True})

for m in source_imports:
 if m.startswith('ImbalancedChen.'):assert m in borrows
save(out/'BORROWED_OBJECTS.json',borrows)
save(out/'SOURCE_INPUT.json',{'module':target,'blob':source_blob,'sha256':source_sha,'bytes':len(source),'lines':len(source.decode().splitlines()),'exact_direct_imports':source_imports,'normal_compile_allowed_for':[target],'source_selection_commit_prefix':'3e5ff771','source_selection_blob':'cd3d598ea536575049484de6f66db142176e7cbe','later_Nonunit_root_acceptance_commit':'952caa6e5bb055bb5a4ed87d1d9855de36e4b35a','project_projection_git_blob':'b7e2341c1d33145e65319b2bf99b375f8bb81715','input_contract_sha256':CONTRACT_SHA256,'existing_sources_unchanged':True,'new_mathematical_sources':0})
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
for part in base_old_inputs['parts']:
 if part['authority']=='actual_pinned_mathlib_package':
  provider=part['provider'];pkg=P(provider['checkout'])
  if str(pkg)not in package_bindings:
   git=lambda *args:subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
   assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and git('rev-parse','HEAD')==package_revisions[provider['name']]==provider['revision']
   package_bindings[str(pkg)]={k:provider[k]for k in ['name','revision','checkout']}
reuse={'schema':'p29_omitted_reuse_existing_qualified_suppliers_v1','status':'REUSED_PRIOR_PASS_BYTES_STABLE_NO_REQUALIFICATION','original_receiver_root':str(oldbase),'original_evidence_archive_sha256':'06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f','original_receipts':{str(oldout/n):h for n,h in old_receipts.items()},'original_supply_receipt':old_supply,'old_qualified_module_count':18,'old_qualified_owned_count':394,'selected_old_P3_input_parts_rehashed_unchanged':len(base_old_by_part),'old_P3_project_modules_selected':contract['base_P3_qualification']['selected_project_modules'],'original_P3_qualified_parts':original_P3_qualified_input_count,'qualified_extra_authorities':authority_summaries,'combined_authority_parts':len(old_by_part),'input_contract_sha256':CONTRACT_SHA256,'new_supplier_source_compilations':0,'new_supplier_named_kernel_replays':0,'new_supplier_owned_replays':0,'new_proof_credit':0,'new_receiver_borrowed_map_sha256':sha(out/'BORROWED_OBJECTS.json'),'original_guard_runner_validator_unchanged':tools_expected}
save(out/'REUSED_SUPPLY_QUALIFICATION.json',reuse)
print(json.dumps({'stage':'existing-supply-reused','selected_project_modules':58,'selected_old_P3_projects':1,'old_P3_qualified_modules':18,'old_owned':394,'new_supplier_replays':0,'new_supplier_source_compilations':0}),flush=True)


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
  m=row['module'];assert not m.startswith(('MathlibNt.','PrimeNumberTheoremAnd.','Architect.'))or m in qualified_research,('Unqualified research input',m)
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
   elif (m,facet)in old_by_part:
    known=old_by_part[(m,facet)];assert str(p)==known['identity']['path']
    assert st==known['stat_snapshot']and st[2]==known['identity']['bytes']
    digest=sha(p);assert digest==known['identity']['sha256']
    authority=known['authority'];provider=known['provider']
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
 before=actual_inputs('omitted-direct-imports',source_imports)
 bound_before=bind_existing_qualification(before)
 before_part_identities={(p['module'],p['facet']):p['identity']for p in before['parts']}
 expected_part_identities={key:p['identity']for key,p in old_by_part.items()}
 assert len(before_part_identities)==len(before['parts'])and before_part_identities==expected_part_identities,'Combined actual imports must equal the entire selected qualified module/facet map.'
 assert before['module_count']==contract['expected_merged_actual_module_count']and before['part_count']==contract['expected_merged_part_count']
 expected_project=set(m for m in source_imports if m.startswith('ImbalancedChen.'))
 pending=list(expected_project)
 while pending:
  m=pending.pop()
  for dep in borrows[m]['direct_project_imports']:
   if dep not in expected_project:expected_project.add(dep);pending.append(dep)
 actual_project={r['module']for r in before['actual_modules']if r['module'].startswith('ImbalancedChen.')}
 assert actual_project==expected_project==set(contract['expected_merged_project_modules'])and len(actual_project)==58
 stable()
 save(out/'PRE_NORMAL_INPUT_BINDING.json',{'source_git_blob':source_blob,'source_sha256':source_sha,'direct_imports':source_imports,'actual_import_bindings_sha256':sha(out/'omitted-direct-imports-bindings.json'),'same_existing_qualification_parts':bound_before,'actual_project_modules':sorted(actual_project),'reused_original_18_supply_receipt_sha256':sha(oldout/'SUPPLY_QUALIFICATION.json'),'current_reuse_receipt_sha256':sha(out/'REUSED_SUPPLY_QUALIFICATION.json'),'new_supplier_replays':0,'new_supplier_source_compilations':0})
 normal_cmd=runprefix+['lake','env','lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(lib/(target.replace('.','/')+'.olean')),'-i',str(lib/(target.replace('.','/')+'.ilean')),str(src)]
 normal=stage('normal-build',normal_cmd,allow_sources={str(src.resolve())},timeout=900)
 produced=source_outputs();save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',produced)
 after=actual_inputs('consumer-actual-imports',[target],produced)
 bound_after=bind_existing_qualification(after,allow_target=True)
 assert bound_after==bound_before
 after_old_part_identities={(p['module'],p['facet']):p['identity']for p in after['parts']if p['module']!=target}
 assert after_old_part_identities==before_part_identities==expected_part_identities,'An old module/facet identity or hash changed, disappeared or appeared after target normal.'
 assert len(after['parts'])==len(after_old_part_identities)+sum(p['module']==target for p in after['parts'])
 assert {(p['module'],p['facet'])for p in after['parts']if p['module']==target}=={(target,'.olean')}
 save(out/'BEFORE_AFTER_EXACT_OLD_PART_IDENTITY_CHECK.json',{'schema':'p29_omitted_exact_old_module_facet_identity_preservation_v1','old_part_count':len(before_part_identities),'pre_normal_graph_sha256':sha(out/'omitted-direct-imports-bindings.json'),'post_normal_graph_sha256':sha(out/'consumer-actual-imports-bindings.json'),'selected_union_part_map_sha256':contract['expected_merged_part_map_sha256'],'every_old_module_facet_path_bytes_sha256_identical':True,'only_added_part':[target,'.olean'],'old_source_kernel_owned_replays':0})
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
 result={'schema':'p29_omitted_prime_wall_P3_normal_named_kernel_full_owned_v1','result':'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED','module':target,'source_git_blob':source_blob,'source_sha256':source_sha,'source_bytes':len(source),'normal':normal,'kernel':kernel,'owned':owned,'owned_count':len(decls),'inventory':inventory,'observed_axioms':axioms,'all_owned_private_generated_types_and_universes':True,'actual_input_modules':after['module_count'],'actual_input_parts':after['part_count'],'actual_input_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'pre_normal_import_bindings_sha256':sha(out/'omitted-direct-imports-bindings.json'),'existing_qualified_input_parts_used':bound_after,'before_after_complete_old_part_identity_check_sha256':sha(out/'BEFORE_AFTER_EXACT_OLD_PART_IDENTITY_CHECK.json'),'selected_project_projection_sha256':contract['project_projection']['sha256'],'original_guard_runner_validator_unchanged':tools_expected,'source_and_outputs_unchanged_after_normal':True,'monitored_parts_unchanged':len(cache_before),'normal_source_invocations':lean_sources,'borrowed_source_recompilations':0,'borrowed_module_count':len(borrows),'original_18_borrowed_module_count':18,'qualified_extra_authorities':authority_summaries,'input_contract_sha256':CONTRACT_SHA256,'existing_Unit_Gate_source_kernel_owned_replays':0,'borrowed_modules_actually_used':sorted(expected_project),'borrowed_new_kernel_replays':0,'borrowed_new_owned_replays':0,'original_supply_receipt_sha256':sha(oldout/'SUPPLY_QUALIFICATION.json'),'current_supply_reuse_receipt_sha256':sha(out/'REUSED_SUPPLY_QUALIFICATION.json'),'direct_Lean_outputs':['.olean','.ilean'],'no_Lake_trace_or_setup_created':True,'no_existing_Unit_evidence_modified':True,'full_P2_9_complete':False,'whole_standard_import_kernel_replay_claim':False,'scope':'Exact original OmittedPrimeWall source: reserve one omitted prime coordinate and combine the original affine-wall measure estimate with the accepted nonunit quotient. Preserve all tuple order, whole-product coprimality, ranks and quantifiers. No source edits, outside-manuscript lemmas, signed-PP input, or full P2.9 completion.'}
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','module','owned_count','observed_axioms','actual_input_modules','actual_input_parts']}),flush=True)
except Exception as e:
 partial={str(p):{'bytes':p.stat().st_size,'sha256':sha(p)}for p in [src,lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]if p.is_file()}
 failure={'schema':'p29_omitted_prime_wall_P3_gate_failure_v1','root':str(root),'evidence':str(out),'source_git_blob':source_blob,'source_sha256':source_sha,'error':str(e),'traceback':traceback.format_exc(),'completed_stages':[r['stage']for r in runs],'changed_protected_parts':[p for p,s in cache_before.items()if not P(p).is_file()or stamp(p)!=s],'partial_target_outputs_preserved':partial,'existing_supply_qualification_reused':True,'supplier_recompilations':0,'supplier_kernel_owned_replays':0}
 save(out/'FAILURE.json',failure);print(json.dumps(failure),flush=True);raise
members={}
for p in out.rglob('*'):
 if p.is_file():
  assert not p.is_symlink();members['verification/'+str(p.relative_to(out))]=p
for p in [src,root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json',lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]:
 assert p.is_file()and not p.is_symlink();members['project/'+str(p.relative_to(root))]=p
for p in (base/'original-tools').iterdir():members['original-tools/'+p.name]=p
manifest={k:{'bytes':p.stat().st_size,'sha256':sha(p)}for k,p in members.items()}
save(base/'FILE_MANIFEST.json',{'schema':'p29_omitted_complete_current_receiver_evidence_v1','files':manifest,'excludes':['FILE_MANIFEST.json'],'borrowed_original_18_evidence_archive_sha256':'06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f','borrowed_symlinks_not_packaged_as_new_objects':True,'no_old_supplier_source_kernel_owned_replay':True})
members['FILE_MANIFEST.json']=base/'FILE_MANIFEST.json'
archive=base/'qualified-omitted-prime-wall.tar.xz'
with tarfile.open(archive,'w:xz',preset=6)as t:
 for name,p in sorted(members.items()):t.add(p,arcname=name,recursive=False)
meta={'path':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),'members':len(members),'manifest_sha256':sha(base/'FILE_MANIFEST.json'),'new_module':target,'new_owned_count':len(decls),'old_supplier_owned_count_reused_without_replay':394}
save(base/'ARCHIVE_TRANSPORT.json',meta);print('P29_ARCHIVE '+json.dumps(meta),flush=True)
