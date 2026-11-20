"""Check frozen selected source bytes and literal Fine-to-density bindings.

Source and lexical verification only: no Lean elaboration, kernel replay,
certificate evaluation or independent mathematical proof review.
"""
import hashlib, json, re
from collections import deque
from pathlib import Path

root=Path('/tmp/p4a4-phase23')
receipts=root/'receipts'
selected=root/'selected'

def gitblob(path):
    b=path.read_bytes()
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

expected_receipts={
 'T01_FINE_COFINAL_ALLOWLIST.json':'7cd063beed2b1f6d0df8306749e02ab84ffeb081',
 'INSTALLATION_OVERLAYS.json':'7cb0603d19b8a5531bbfc2dc03defe017068d6c0',
 'FINAL_FINE_REGISTRY.json':'3df38dd53910d751d7511d287b2c6d8eb1cdca2a',
 'FINAL_HDENSITY_REGISTRY.json':'268590feda6738d78f335fb6b786e0a668f7ec0d',
 'SOURCE_SELECTION.json':'a635b1de48ebef80d11c365c4a78261199758b9f',
 'P4AOriginalFiniteAll22FineDensity.lean':'70edb851800f82f3e809b89d83559f22b649607d',
 'SOURCE_SELECTION_PHASE15.json':'a951cbf01691b2f38915ac3dd2ea608d9d92e1b0',
 'CANDIDATE_IDENTITY_PHASE16.json':'b1cd3789d02960e272fa7b0d02a9925e27ad1dd4',
}
for n,sha in expected_receipts.items(): assert gitblob(receipts/n)==sha,n
allow=json.loads((receipts/'T01_FINE_COFINAL_ALLOWLIST.json').read_text())
overlays=json.loads((receipts/'INSTALLATION_OVERLAYS.json').read_text())
fine_reg=json.loads((receipts/'FINAL_FINE_REGISTRY.json').read_text())
density_reg=json.loads((receipts/'FINAL_HDENSITY_REGISTRY.json').read_text())
publication=json.loads((receipts/'SOURCE_SELECTION.json').read_text())
high=allow['existing_high_sources_reached_within_that_record']
early=overlays['selected_early12_install_order']
assert len(high)==len(early)==12
assert set(allow['outside_this_use_within_high14'])=={
 'P4AOriginalFiniteFallbackGroupedAtoms','P4AOriginalFiniteFallbackJointHigh'}
rows=[]
def record(group,name,bytes_,sha256,blob):
 p=selected/name
 b=p.read_bytes()
 assert len(b)==bytes_,name
 assert hashlib.sha256(b).hexdigest()==sha256,name
 assert gitblob(p)==blob,name
 rows.append({'group':group,'name':name,'bytes':bytes_,'sha256':sha256,'git_blob':blob})
for x in high:
 record('fine_high_12',Path(x['installation_target']).name,x['bytes'],x['sha256'],x['git_blob_sha1'])
for x in early:
 record('early_12',Path(x['install_path']).name,x['bytes'],x['sha256'],x['git_blob_sha1'])
scope=overlays['namespace_overlay']['staged_source']
record('namespace_overlay','P4AOriginalOrderedThirdFullPolicy.lean',scope['bytes'],scope['sha256'],scope['git_blob_sha1'])
x=fine_reg['new_source']
record('fine_terminal',Path(x['install_path']).name,x['bytes'],x['sha256'],x['git_blob_sha1'])
for x in allow['direct_imports']:
 n=Path(x['path']).name
 if n=='P4AOriginalFiniteFallbackAllHighAtoms.lean': continue
 record('fine_direct',n,x['bytes'],x['sha256'],x['git_blob_sha1'])
assert len(rows)==28 and len({r['name'] for r in rows})==28
old_selection=json.loads((receipts/'SOURCE_SELECTION_PHASE15.json').read_text())
candidate_receipt=json.loads((receipts/'CANDIDATE_IDENTITY_PHASE16.json').read_text())
u=next(x for x in old_selection['source_rows'] if x['module']=='ImbalancedChen.P1OriginalFourthUniformCutoffLicence')
record('selected_uniform_cutoff','P1OriginalFourthUniformCutoffLicence.lean',u['bytes'],u['sha256'],u['git_blob'])
candidates=[]
for name in ['P1OriginalFourthSameScheduleLicence','P1OriginalFourthActualQuantizedLicence']:
 x=next(x for x in candidate_receipt['candidate_rows'] if x['module']=='ImbalancedChen.'+name)
 p=root/'candidate'/(name+'.lean'); b=p.read_bytes()
 assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256'] and gitblob(p)==x['git_blob']
 assert x['selection_status']=='CANDIDATE_ONLY_NO_SELECTION_AUTHORITY'
 assert {'62af0da0e7668d17d1add82141f009b89010211a','71b47b30928600386237323d4f6a1f0c332edfbe'} <= {y['ref'] for y in x['same_tree_refs'] if y['blob']==x['git_blob']}
 candidates.append({'module':x['module'],'git_blob':x['git_blob'],'sha256':x['sha256'],
                    'candidate_path':x['packet_path'],'selection_status':x['selection_status']})

# Trace a concrete early G1 dependency until the first absent selected module.
graph={p.stem:re.findall(r'^import ImbalancedChen\.([A-Za-z0-9_]+)',p.read_text(),re.M)
       for p in selected.glob('*.lean')}
start='P4AOriginalFiniteAll22FineCofinalCoefficient'; goal='P1OriginalFourthSameScheduleLicence'
queue=deque([(start,[start])]); visited=set(); path=None
while queue:
 n,trail=queue.popleft()
 if n==goal: path=trail; break
 if n in visited: continue
 visited.add(n)
 queue.extend((child,trail+[child]) for child in graph.get(n,[]) if child not in visited)
assert path is not None and path[-2]=='P1OriginalFourthUniformCutoffLicence'
assert not (selected/(goal+'.lean')).exists()
same=(root/'candidate'/'P1OriginalFourthSameScheduleLicence.lean').read_text()
quant=(root/'candidate'/'P1OriginalFourthActualQuantizedLicence.lean').read_text()
winner=same.split('theorem actual_fourth_original_winner_same_schedule',1)[1].split(' := by',1)[0]
assert '2*(e : ℝ)+2*width n < commonMargin' in winner and 'width n ≤ 2*(e : ℝ)' not in winner
assert 'width n ≤ 2*(e : ℝ)' in quant
uniform=(selected/'P1OriginalFourthUniformCutoffLicence.lean').read_text().split('theorem exists_same_schedule_uniform_cutoff_fourth',1)[1].split(' := by',1)[0]
assert uniform.index('∀ mMin qMin')<uniform.index('∃ q0')<uniform.index('∀ omega')<uniform.index('∀ r ∈ originalRows4')

# Verify the high-12 subgraph only, not all transitive imports.
high_names={Path(x['installation_target']).stem for x in high}
imports={name:set(re.findall(r'^import ImbalancedChen\.([A-Za-z0-9_]+)',
                  (selected/(name+'.lean')).read_text(),re.M)) for name in high_names}
seen=set(); todo=['P4AOriginalFiniteFallbackAllHighAtoms']
while todo:
 n=todo.pop()
 if n in seen: continue
 seen.add(n)
 todo.extend((imports[n]&high_names)-seen)
assert seen==high_names

fine=(selected/'P4AOriginalFiniteAll22FineCofinalCoefficient.lean').read_text()
density=(receipts/'P4AOriginalFiniteAll22FineDensity.lean').read_text()
assert density_reg['new_source']['git_blob_sha1']==expected_receipts['P4AOriginalFiniteAll22FineDensity.lean']
assert 'import ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient' in density
assert density.count('P4AOriginalFiniteAll22FineCofinalCoefficient.exists_fine_cofinal_same_coefficient_density_and_count')==1
assert '(densityReserve/2) eMax (half_pos densityReserve_pos) heMax' in density
assert 'moduli N ((N:ℝ)^(nu*beta^2))' in density
assert 'P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a (nu*beta^2) N' in density
assert '(alignedWidth (jointIndex (bank m) (data e q a).m) k) ((N:ℝ)^(nu*beta))' in density
assert 'let Q := moduli N w' in fine
assert 'let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L' in fine
assert 'realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1)' in fine
assert 'realPhysicalDistributionError b N T (Q 0 N) (rho 0 N)+(Nat.ceil z:ℝ)+(T+1)' in density
assert 'P4AOriginalFiniteFallbackActualTaggedRate' not in density
assert density_reg['whole_PP_paid'] is False and density_reg['kernel_verified'] is False
assert fine_reg['full_transitive_installation_complete'] is False
assert len(publication['rows'])>0
out={'schema':'p4a4-fine-consumer-source-identities-phase23-v1',
 'baseline':'26221784d1deac1b11c260b109aa843bee993edf',
 'source_ref':'71b47b30928600386237323d4f6a1f0c332edfbe',
 'verified_selected_rows':rows,'fine_high_graph_reached':sorted(seen),
 'excluded_high14_only_for_this_fine_use':allow['outside_this_use_within_high14'],
 'consumer_source_blob':expected_receipts['P4AOriginalFiniteAll22FineDensity.lean'],
 'early_import_path_to_first_isolated_candidate':path,
 'isolated_candidates':candidates,
 'consumer_scope':'Calls original Fine once at densityReserve/2. Q and rho are literal delta-constant families, with the same q/beta/k; correction and finite signed distribution error are retained. The phase22 tag rate is not imported here.',
 'source_only':True,'compiled':False,'kernel_replayed':False,
 'transitive_axioms_checked':False,'independent_review_this_run':False,
 'scope':'Selected 29 source bytes, two isolated candidate bytes, restricted high-12 name graph, one exact early import path and literal source markers only; no whole dependency closure, Lean elaboration or proof evaluation.'}
(root/'CONSUMER_SELECTION_AUDIT_PHASE23.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print('receipt_git_blobs',len(expected_receipts))
print('selected_source_bytes_verified',len(rows))
print('fine_high_subgraph_reached',len(seen))
print('early_dependency_path_length',len(path),'first_missing_selected',goal)
print('isolated_candidate_bytes_verified',len(candidates))
print('outside_this_fine_use',','.join(sorted(allow['outside_this_use_within_high14'])))
print('source_binding_and_error_markers pass')
print('Lean_elaboration_or_kernel false')
