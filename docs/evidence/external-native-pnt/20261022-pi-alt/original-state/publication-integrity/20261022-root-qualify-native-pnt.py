"""Root qualification of a selected existing native supplier, not project ownership."""
from pathlib import Path
import hashlib,json,datetime
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'.lake/proof-continuation'
M='PrimeNumberTheoremAnd.Consequences'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def checked(name,digest):
    p=S/name;assert sha(p)==digest,name
    return p
def read(p):return json.loads(p.read_bytes())
def ref(p):return {'path':p.relative_to(S).as_posix(),'sha256':sha(p)}
before=checked('rounds/native-pnt-inputs-20261022-v1/before.json','274be1bd2e6e3d42fb508e6c3ee2af5b22ac759120f15a829ece5ac55f0f8540')
after=checked('rounds/native-pnt-inputs-20261022-v1/after.json','3a513879df97bd3081f4925cf120dc51f8ea9044964c04a7cc95945bb589a0c1')
b=read(before);a=read(after);x=b['inputs']
assert b['phase']=='before' and a['phase']=='after' and a['deep_exact_against_before'] is True
assert x==a['inputs'] and len(x['native_nodes'])==6029 and len(x['project_sources562'])==562
assert len(x['STATE_cache_and_lib_map'])==690
assert x['collector']['sha256']=='1728938a91a0a612bf849bbb77435b2da7bf878ac02d1fcb5d0409c8663e26a0'
rp=checked('audits/20261022T023156467636Z/receipt.json','41dfaf5283c0c1d532eedc7b213117b27f8be1244bf2bf24ff322492a5ed8f89')
d=rp.parent;r=read(rp)
assert r['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS'
assert r['targets']=={M:x['source_sha256']}
assert r['inputs_before']==r['inputs_after']
assert r['inputs_before']['pins']==x['pins']
assert r['inputs_before']['sources']==r['targets']
parts={k:v for k,v in x['native_nodes'][M]['all_five_slots'].items() if v is not None}
assert r['inputs_before']['owned_object_parts']=={M:parts}
assert r['inputs_before']['lean_real_sha256']==x['native_bins']['lean.real']
assert r['inputs_before']['checker_sha256']==x['native_bins']['leanchecker']
assert not r['external_closure_replay_claimed'] and not r['unconditional_main_claimed']
assert r['audit_runner_sha256']==sha(S/'audit_owned.py')=='267d59bfc37e5d5a742b619390f5b42155bb5ab33d923684487acb6b8a7e19e6'
assert r['source_template_sha256']==sha(ROOT/'verification/parts/p0/queue/AuditTemplate.lean')=='df79aecf54317dbdc193e9b68ec8e833f6d4d09a92f369ac6985d23d974ff822'
assert r['generated_audit_sha256']==sha(d/'OwnedAudit.lean')
stocks=[z for z in r['stages'] if z['kind']=='stock_replay']
types=[z for z in r['stages'] if z['kind']=='full_inventory_type_axioms']
assert len(stocks)==len(types)==1 and stocks[0]['module']==M and types[0]['exit_code']==0
stock=stocks[0]['result'];ap=read(d/'audit-process.json')
for process in (stock,ap):
    assert process['status']=='PASS' and process['returncode']==0 and process['guard_error'] is None
    assert process['rss_guard']['limit_mib']==6656 and process['max_rss_kib']<=6656*1024
assert ap['command'][1:4]==['-j2','-M6144','-DwarningAsError=true']
assert stock['log_sha256']==sha(d/('replay-'+M+'.log'))
assert types[0]['log_sha256']==sha(d/'declarations.log')
inventories={};emitted={}
for line in (d/'declarations.log').read_text(encoding='utf-8').splitlines():
    if line.startswith('P0_QUEUE_INVENTORY '):
        v=json.loads(line.split(' ',1)[1]);assert v['module'] not in inventories;inventories[v['module']]=v
    if line.startswith('P0_QUEUE_DECL '):
        v=json.loads(line.split(' ',1)[1]);assert v['name'] not in emitted;emitted[v['name']]=v
records=read(d/'declarations.json')
assert len(records)==len(emitted)==r['declaration_counts'][M]==339
assert {z['name']:z for z in records}==emitted and set(inventories)=={M}
inventory=inventories[M]
assert len(inventory['serialized'])==len(set(inventory['serialized']))==len(inventory['environment'])==len(set(inventory['environment']))==339
assert set(emitted)==set(inventory['serialized'])==set(inventory['environment'])
for record in records:
    assert record['module']==M and record['type'] and '⋯' not in record['type']
    assert not(record['unsafe'] or record['partial'] or record['axiom'])
    assert set(record['axioms'])<={'propext','Classical.choice','Quot.sound'}
supplier=emitted['pi_alt']
assert supplier['type'].startswith('@Exists.{1} (Real → Real)')
assert 'Nat.primeCounting' in supplier['type'] and 'Nat.floor' in supplier['type'] and 'Real.log x' in supplier['type']
out=S/'source-reviews/20261022-root-native-pnt-pi-alt-scoped-qualification.json'
value={'status':'ROOT_QUALIFIED_EXISTING_NATIVE_PNT_SUPPLIER_SCOPED_STOCK_ALL',
    'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'module':M,'supplier':supplier,'source_sha256':x['source_sha256'],'object_parts':parts,
    'original_proper':x['original_proper'],'before':ref(before),'after':ref(after),'original_audit':ref(rp),
    'declarations_json':ref(d/'declarations.json'),'declarations_log':ref(d/'declarations.log'),
    'actual_complete_native_declarations':339,'all_native_input_nodes':6029,
    'all_inputs_before_after_deep_exact':True,'actual_singleton_stock_invocations':1,'retry_count':0,
    'root_type_review':'Root read full pp.all pi_alt: exact all-real existential hPNT supplier, no additional hypothesis.',
    'external_qualification_scope':'Selected existing native module stock replay, complete serialized inventory/types, safety and reported transitive axiom metadata under fixed native-library trust.',
    'fresh_nine_module_import_closure_replayed':False,'historical_strict_producer_reproduced':False,
    'project_bridge_materialized':False,'hPNT_consumers_discharged':False,
    'owned_modules_added':0,'owned_modules':190,'declarations':4327,'original_owned_receipts':138,
    'unconditional_main_proved':False,'weighted_mathematical_progress':30}
with out.open('x',encoding='utf-8',newline='\n') as f:f.write(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'qualification':ref(out),'external_supplier':'pi_alt','native_declarations':339,'owned_added':0}))
