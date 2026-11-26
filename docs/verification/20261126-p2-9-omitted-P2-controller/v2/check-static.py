import ast,base64,hashlib,json,pathlib,zlib,difflib,collections
R=pathlib.Path('/dev/shm/p29-omitted-controller-1126')
W=pathlib.Path('/workspace/scratch/005887317b49')
def pin(path,size,sha):
 b=path.read_bytes()
 assert len(b)==size and hashlib.sha256(b).hexdigest()==sha
 return b
s1=pin(R/'omitted-prime-wall-P2-controller-v1.py',61761,'e14f1426c196d846a757ad40d90a07e12cfeb19b230032fa6155594e65c51aa4')
s2=pin(R/'omitted-prime-wall-P2-controller-v2.py',64804,'945a19ceecfd707c5fa801ca9ce4f170755c9bbe363079293198e40bacc09970')
c1=pin(R/'OMITTED_P2_INPUT_CONTRACT.json',13235,'61ade535a3221cc03553bb02f719c6df244e14096b7960e440d84ba7dd94520c')
c2=pin(R/'OMITTED_P2_INPUT_CONTRACT_V2.json',15390,'1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf')
w2=pin(R/'omitted-prime-wall-P2-controller-v2-command-template.sh',35090,'b41003ec70cc5d1d183202aa86b4bc866f67a314387bd5a70a8ab2ca918a0e40')
for before,after,name,labels in [(s1,s2,'OMITTED_P2_PORT_V1_TO_V2.patch',['fixed-P2-concrete-v1','fixed-P2-concrete-v2']),(c1,c2,'OMITTED_P2_CONTRACT_V1_TO_V2.patch',['contract-v1','contract-v2'])]:
 expected=''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile=labels[0],tofile=labels[1]))
 assert expected==(R/name).read_text()
astdump=lambda n:ast.dump(n,include_attributes=False)
f1={n.name:n for n in ast.parse(s1).body if isinstance(n,ast.FunctionDef)}
f2={n.name:n for n in ast.parse(s2).body if isinstance(n,ast.FunctionDef)}
assert f1.keys()==f2.keys()
unchanged=[n for n in f1 if n!='main']
assert all(astdump(f1[n])==astdump(f2[n])for n in unchanged)
C1=json.loads(c1);C2=json.loads(c2)
C2copy=json.loads(c2)
del C2copy['authorities']['P2_received18_path_binding']
del C2copy['authorities']['original_P1_profile_project_rows']
del C2copy['resolved_foreign_direct_imports']
assert C2copy==C1
lines=w2.decode().splitlines(True)
assert lines[0]=="python3 - <<'PY'\n" and lines[-1]=='PY\n'
wt=ast.parse(''.join(lines[1:-1]))
assert len(wt.body)==6 and [type(n).__name__ for n in wt.body]==['Import','Assign','Assign','Assign','Assert','Expr']
for i,name,expected in [(1,'source',s2),(2,'contract',c2)]:
 n=wt.body[i];assert ast.unparse(n.targets[0])==name and len(n.targets)==1
 outer=n.value;assert ast.unparse(outer.func)=='zlib.decompress' and len(outer.args)==1 and not outer.keywords
 inner=outer.args[0];assert ast.unparse(inner.func)=='base64.b64decode'and len(inner.args)==1 and not inner.keywords
 assert zlib.decompress(base64.b64decode(ast.literal_eval(inner.args[0]),validate=True))==expected
assert ast.unparse(wt.body[3])=="observation = zlib.decompress(base64.b64decode('__SERVICE_OBSERVATION_ZLIB_BASE64__'))"
call=wt.body[-1].value
assert ast.unparse(call.func)=='exec'and len(call.args)==2 and not call.keywords
assert ast.unparse(call.args[0])=="compile(source, 'omitted-prime-wall-P2-controller-v2.py', 'exec')"
assert [ast.literal_eval(k)for k in call.args[1].keys]==['__name__','SOURCE_TEXT','SOURCE_SHA256','INPUT_CONTRACT_TEXT','SERVICE_OBSERVATION_JSON','SERVICE_OBSERVATION_SHA256']
assert [ast.unparse(v)for v in call.args[1].values]==["'__main__'",'source.decode()',repr(hashlib.sha256(s2).hexdigest()),'contract.decode()','observation.decode()',"'__SERVICE_OBSERVATION_SHA256__'"]
expected_assert="assert hashlib.sha256(source).hexdigest()=="+repr(hashlib.sha256(s2).hexdigest())+" and hashlib.sha256(contract).hexdigest()=="+repr(hashlib.sha256(c2).hexdigest())+" and hashlib.sha256(observation).hexdigest()=='__SERVICE_OBSERVATION_SHA256__'"
assert astdump(wt.body[4])==astdump(ast.parse(expected_assert).body[0])
assert b'\0'not in w2 and len(w2)<65536
req=json.loads((R/'OMITTED_P2_REQUEST_TEMPLATE_V2.json').read_bytes())
assert {k:req[k]for k in ['cwd','memory_mb','cpu_threads','timeout_seconds']}=={'cwd':'/workspace','memory_mb':12800,'cpu_threads':2,'timeout_seconds':3600}
assert req['source']['sha256']==hashlib.sha256(s2).hexdigest()and req['input_contract']['sha256']==hashlib.sha256(c2).hexdigest()and req['command_template']['sha256']==hashlib.sha256(w2).hexdigest()
raw=json.loads(pin(W/'p29-current/omitted-p2-byte-receiver/P2_OMITTED18_BYTE_RECEPTION_RECEIPT.json',84932,'855300937a4938f0a83fa1127476abd87263161d51a885ef4fad86a5a693838b'))
binding=json.loads(pin(W/'p29-current/omitted-p2-byte-receiver/P2_OMITTED18_RECEPTION_BINDING.json',20692,'ccec77943f9a98e1fca5dbe8264bd7d90be0c5e90962c27ef06ac4315b5251b7'))
rows=binding['selected_objects'];received={r['module']:r for r in rows}
assert len(rows)==len(received)==18 and set(received)==set(raw['selected_objects'])
assert binding['complete_receipt']['sha256']==C2['authorities']['P2_received18']['sha256']
for mod,row in received.items():
 orig=raw['selected_objects'][mod]
 assert row['path']==orig['selected_path']and row['stat']==orig['final_stat']
 assert row['bytes']==orig['bytes']and row['sha256']==orig['sha256']and row['selection']==orig['selection']
 assert (row['source']==orig['source_received'])if 'source'in row else ('source_received'not in orig)
 assert row['kind']==('foreign_project'if mod.startswith('ImbalancedChen.')else'native')
selected=json.loads(pin(W/'p29-atlas-1126/OMITTED_SELECTIVE_58_PROJECT_SUPPLIER_PROJECTION.json',51530,'6e17baca207d13c563770fd5f2303bef05bb00488e47cb120e02eb31949fc55f'))['selected_modules']
original=json.loads(pin(W/'p29-current/p1-profile-qualified-portable/evidence/BORROWED_OBJECTS.json',63987,'01f254264580b22f22c2e20caaba30b13d309656099d7127f49e2d6cb5022562'))['objects']
imports={}
for mod,row in selected.items():
 value=row['direct_project_imports']
 if isinstance(value,list):
  imports[mod]=value
 else:
  assert value=='not_a_field_in_this_original_borrowed_row_do_not_interpret_as_empty'
  fixed=C2['resolved_foreign_direct_imports'][mod]
  assert fixed['source_sha256']==row['source_sha256']==original[mod]['source_sha256']
  assert fixed['object_sha256']==row['object_sha256']==original[mod]['object_sha256']
  deps=fixed['direct_project_imports']
  assert fixed['dependency_byte_pins_from_original_qualified_rows']=={m:original[m]['object_sha256']for m in deps}=={m:selected[m]['object_sha256']for m in deps}
  if mod.endswith('.P2FiniteMarkedGamma5FrozenConstants'):
   assert deps==raw['selected_objects'][mod]['provenance']['original_borrow_record']['direct_project_imports']==[]
  imports[mod]=deps
assert len(C2['resolved_foreign_direct_imports'])==2
assert all(dep in selected for deps in imports.values()for dep in deps)
nativebytes=pin(pathlib.Path('/tmp/p29-ad438-snapshot-offline-1126/NATIVE_SOURCE_IMPORTS.jsonl'),590398,'c0d4b13bb7a404faec17e7aa8389eef5fe8783ecb3060e07d785963af2ac80d5')
native=[json.loads(line)['module']for line in nativebytes.splitlines()]
extra={m for m,r in received.items()if r['kind']=='native'}
foreign={m for m,r in received.items()if r['kind']=='foreign_project'}
assert len(native)==len(set(native))==515 and len(extra)==14 and not set(native)&extra
assert len(foreign)==4 and len(selected)==58
assert foreign=={m for m,r in selected.items()if r['origin']!='P2_saving16_original_normal_record'}
assert not (set(native)|extra)&set(selected)
result={'status':'PASS_INCREMENTAL_STATIC_AND_SMALL_METADATA_JOIN',
'original_non_main_functions_AST_unchanged':len(unchanged),
'complete_source_and_contract_diffs_exact':True,
'resource7_unchanged':True,
'wrapper6_AST_source_contract_and_globals_exact':True,
'request_exact':{k:req[k]for k in ['cwd','memory_mb','cpu_threads','timeout_seconds']},
'wrapper_template_bytes':len(w2),'final_observation_wrapper_still_pending':True,
'raw18_to_path_binding_exact':True,
'resolved_import_sentinels':sorted(C2['resolved_foreign_direct_imports']),
'all_project_deps_within58_after_exact_recovery':True,
'project58_original54_plus_received4':True,
'native529_original515_plus_received14':True,
'project_native_name_collision':False,
'native_namespace_counts':dict(collections.Counter(n.split('.')[0]for n in set(native)|extra)),
'remote_or_Lean_execution':False,'large_actual_graph_reads':0,
'proof_qualification_semantics_not_reaudited':True}
print(json.dumps(result,indent=2))
