from pathlib import Path
import ast,hashlib,json
P=Path
root=P('/workspace/p29-nonunit-quotient-20261126-0117dd4')
out=P('/workspace/p29-nonunit-quotient-verification-20261126-0117dd4')
sha=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest()
def stamp(p):
 s=P(p).stat();return[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def ident(p):
 p=P(p);before=stamp(p);h=sha(p);assert before==stamp(p);return{'path':str(p),'bytes':before[2],'sha256':h,'stat':before}
assert sha(out/'driver.py')=='c970948d0848815c2d8dd4462c506e6842efc60415df5b2a9bfc3e14c881ebba'
files={str(p.relative_to(out)):ident(p)for p in sorted(out.rglob('*'))if p.is_file()}
state=json.loads((out/'runtime-evidence/state.json').read_text())
guardlog=P(state['log']);raw_guard=guardlog.read_bytes();assert raw_guard.endswith(b'\n')
commands=[json.loads(l)for l in raw_guard.splitlines()if l]
source_calls=[str((P(r['cwd'])/a).resolve())if not P(a).is_absolute()else str(P(a).resolve())for r in commands if r.get('tool')=='lean'for a in r.get('input_args',[])if str(a).endswith('.lean')]
module='ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient'
src=root/(module.replace('.','/')+'.lean');assert sha(src)=='6b11d4a2bc7838dbdda9e1354b796f659d7782dbd3d62fcec372f49f898611ef'
assert source_calls==[str(src)]
process=json.loads((out/'normal-build-process.json').read_text());assert process['exit_code']==1 and process['forbidden_source_calls']==[]
assert process['log_sha256']==sha(out/'normal-build.log')
failure=json.loads((out/'FAILURE.json').read_text());assert failure['old_evidence_changed']==[]and failure['borrowed_cache_changed']==[]
reuse=json.loads((out/'EXACT_SUPPLIER_REUSE.json').read_text());assert reuse['status']=='PASS_EXACT_MERGED_INPUTS_WITHOUT_SUPPLIER_REPLAY'
bindings_path=out/'merged-supplier-actual-imports-bindings.json';assert reuse['actual_bindings_sha256']==sha(bindings_path)
bindings=json.loads(bindings_path.read_text());summary={k:bindings[k]for k in ['schema','roots','module_count','part_count','counts']};del bindings
tree=ast.parse((out/'driver.py').read_text());pins=next(ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and isinstance(n.targets[0],ast.Name)and n.targets[0].id=='IMMUTABLE_PINS')
assert all(sha(p)==h for p,h in pins.items())
rel=module.replace('.','/')
paths=[root/'.lake/build/lib/lean'/(rel+s)for s in ['.olean','.ilean','.trace']]+[root/'.lake/build/ir'/(rel+s)for s in ['.c','.setup.json']]
outputs=[{'path':str(p),'exists':p.exists(),**(ident(p)if p.exists()else{})}for p in paths]
result={'schema':'p29_nonunit_001_exact_readonly_resume_snapshot_v1','root':str(root),'evidence':str(out),'controller':ident(out/'driver.py'),'files':files,'target_source':ident(src),'target_outputs':outputs,'normal_process':process,'normal_log_text':(out/'normal-build.log').read_text(),'failure':failure,'exact_supplier_reuse':reuse,'actual_graph_summary':summary,'guard_state':state,'guard_prefix':{'bytes':len(raw_guard),'sha256':hashlib.sha256(raw_guard).hexdigest(),'commands':commands,'source_calls':source_calls},'prior_pins_unchanged':True,'old_suppliers_replayed':0,'new_Lean_calls':0,'filesystem_writes':0}
print(json.dumps(result,indent=2),flush=True)
