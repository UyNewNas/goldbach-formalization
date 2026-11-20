"""Check exact recorded source selection; does not parse or elaborate Lean."""
import hashlib, json, re
from pathlib import Path

p=Path('/tmp/p4a4-phase24'); src=p/'sources'; receipts=p/'receipts'
def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
expected_receipts={
 'SAME_SCHEDULE_REGISTRY.json':'497c5e5e511ef549b11652e2a35360ce6a7d8aec',
 'QUANTIZED_SUPPLEMENT_REGISTRY.json':'f28e877172c441404a402e0bc223e6dc5813df37',
 'UNIFORM_CUTOFF_REGISTRY.json':'f98bdd6d3978dd6dc285613cbc601fc304385463',
}
for n,h in expected_receipts.items(): assert blob((receipts/n).read_bytes())==h,n
same=json.loads((receipts/'SAME_SCHEDULE_REGISTRY.json').read_text())
quant=json.loads((receipts/'QUANTIZED_SUPPLEMENT_REGISTRY.json').read_text())
uniform=json.loads((receipts/'UNIFORM_CUTOFF_REGISTRY.json').read_text())
assert same['status']==quant['status']==uniform['status']=='SOURCE_ONLY_UNCOMPILED_UNEVALUATED_AWAITING_T09_AND_REMOTE'
assert sha((receipts/'SAME_SCHEDULE_REGISTRY.json').read_bytes())==uniform['same_schedule_registry']['sha256']
assert sha((receipts/'QUANTIZED_SUPPLEMENT_REGISTRY.json').read_bytes())==same['conditional_quantized_registry']['sha256']
assert same['source']['sha256']==uniform['same_schedule_source']['sha256']
assert same['source']['bytes']==uniform['same_schedule_source']['bytes']
assert same['source']['imports']==['ImbalancedChen.P1OriginalFourthActualQuantizedLicence']

deps={x['module'].split('.')[-1]:x for x in quant['dependencies']}
records=[('P1OriginalFourthSameScheduleLicence',same['source'],'61698ecbd29aac1f755616fd3b2c7524d8bd8323'),
 ('P1OriginalFourthActualQuantizedLicence',quant['source'],'14688bbdfd2730507e69d46c25ee29dd9663a42e'),
 ('P4AOriginalFull87DataPolicy',deps['P4AOriginalFull87DataPolicy'],'501743ebb0b2cbac47cb9a79e5c86f0cb687cb48'),
 ('P4AOriginalNewFifthUnion',deps['P4AOriginalNewFifthUnion'],'2158b9f294b8b8324acfd328998939fb55ab623d'),
 ('P1GuardFrozenFiniteCapAlgebra',deps['P1GuardFrozenFiniteCapAlgebra'],'e052b72ad4da8933bf50beb5db96602401be22cc'),
 ('P1QuantizedActionLicense',deps['P1QuantizedActionLicense'],'8dbda2675372cb3d846478777090359104d181ab')]
common='docs/source-only/20261110-yellow-closure-10t/'
origins={
 'P1OriginalFourthSameScheduleLicence':('71b47b30928600386237323d4f6a1f0c332edfbe',common+'t02_full87_volume_integral/successor_fourth/P1OriginalFourthSameScheduleLicence.lean'),
 'P1OriginalFourthActualQuantizedLicence':('71b47b30928600386237323d4f6a1f0c332edfbe',common+'t02_full87_volume_integral/successor_fourth/P1OriginalFourthActualQuantizedLicence.lean'),
 'P4AOriginalFull87DataPolicy':('71b47b30928600386237323d4f6a1f0c332edfbe',common+'t03_saved87_actual_gain/P4AOriginalFull87DataPolicy.lean'),
 'P4AOriginalNewFifthUnion':('71b47b30928600386237323d4f6a1f0c332edfbe',common+'t05_all22_actual_density/P4AOriginalNewFifthUnion.lean'),
 'P1GuardFrozenFiniteCapAlgebra':('be2efd01c561080672e6c0ad0ba21638837afe4c','docs/source-only/20261103-full87-finite-parent/P1GuardFrozenFiniteCapAlgebra.lean'),
 'P1QuantizedActionLicense':('be2efd01c561080672e6c0ad0ba21638837afe4c','docs/source-only/20261103-full87-action-licences/P1QuantizedActionLicense.lean'),
}
out=[]
for name,entry,h in records:
 b=(src/(name+'.lean')).read_bytes()
 assert len(b)==entry['bytes'] and sha(b)==entry['sha256'] and blob(b)==h,name
 if 'git_blob' in entry: assert entry['git_blob']==h
 out.append({'module':'ImbalancedChen.'+name,'bytes':len(b),'sha256':sha(b),'git_blob':h,
   'origin_commit':origins[name][0],'origin_path':origins[name][1],
   'packet_path':'docs/source-only/20261119-p4a4-fine-direct-sources/ImbalancedChen/'+name+'.lean',
   'imports':re.findall(r'^import ([^\n]+)',b.decode(),re.M)})
ub=(src/'P1OriginalFourthUniformCutoffLicence.lean').read_bytes()
assert sha(ub)==uniform['source']['sha256'] and len(ub)==uniform['source']['bytes']
assert blob(ub)=='7c59f4e9c5d3f30b74db86776e53bf32a397d616'
S=(src/'P1OriginalFourthSameScheduleLicence.lean').read_text()
Q=(src/'P1OriginalFourthActualQuantizedLicence.lean').read_text()
U=ub.decode()
assert 'import ImbalancedChen.P1OriginalFourthActualQuantizedLicence' in S
assert 'import ImbalancedChen.P1OriginalFourthSameScheduleLicence' in U
assert 'hu.trans_eq hwin' in S
winner=S.split('theorem actual_fourth_original_winner_same_schedule',1)[1].split(' := by',1)[0]
assert '2*(e : ℝ)+2*width n < commonMargin' in winner
assert 'width n ≤ 2*(e : ℝ)' not in winner
assert 'width n ≤ 2*(e : ℝ)' in Q
for name in ['P1OriginalFourthSameScheduleLicence','P1OriginalFourthActualQuantizedLicence']:
 text=(src/(name+'.lean')).read_text()
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',text),name
o={'schema':'p4a4-g1-selected-source-phase24-v1','baseline':'b912f502e5be53ba0c88d4a354da2fc4d0072d45',
 'origin_ref':'71b47b30928600386237323d4f6a1f0c332edfbe','registry_git_blobs':expected_receipts,
 'registered_uniform_cutoff_blob':'7c59f4e9c5d3f30b74db86776e53bf32a397d616',
 'selected_sources':out,'basis':'Uniform registry names exact same-schedule SHA; same-schedule registry names quantized registry; quantized registry names exact support dependencies. Existing source-only candidate bodies are unchanged.',
 'status':'SOURCE_ONLY_UNCOMPILED_UNEVALUATED','transitive_closure_complete':False,'kernel_replayed':False,
 'transitive_axioms_checked':False,'independent_review_this_run':False,
 'caveat':'Source identity and named author registries only. T09 coordination is recorded in source registry but final independent review and Lean verification remain outstanding.'}
(p/'SOURCE_SELECTION_PHASE24.json').write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
print('registered_source_bytes',len(out))
print('uniform_same_schedule_quantized_registry_chain pass')
print('four_explicit_support_dependencies_exact pass')
print('winner_same_schedule_not_width_le_2e pass')
print('lean_elaboration_kernel_axioms_finite_evaluation false')
