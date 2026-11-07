import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,hashlib,re
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');out=root/'.lake/proof-continuation/source-reviews'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py';tree=ast.parse(helper.read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'sha','uncomment','assignment_at_top','declarations'}],type_ignores=[]),str(helper),'exec'))
old=out/'20261016-U8FiniteMean-owner-semantics.json';assert sha(old)=='1f23b0a7b18f5abecf5532cd55a968a1b3dff4b2b92de52cfd9eb3a52b14e546'
report=json.loads(old.read_text());source=root/report['path'];assert sha(source)==report['source_sha256']=='da4d9c59126cc173e38182e4bcc060a6ad082b103906b7c17c8cbed363e2172b'
patches={'Source-independent active-modulus set definition':(159,161),'Public actual positive-modulus active subset':(187,192),'Public generic zero actual AP count for non-coprime multiplier at primitive centre':(48,65),'Public generic arbitrary-positive-multiplier switched fibre upper sieve, with proven complete divisor-sum nonnegativity before source extension':(90,145)}
for api in report['fixed_API_source_evidence']:
    if api['role'] in patches:
        lo,hi=patches[api['role']];p=Path(api['path']);assert sha(p)==api['file_sha256'];api['lines']=[lo,hi];api['literal_source_excerpt']='\n'.join(p.read_text().splitlines()[lo-1:hi])
complete_specs={
'CurrentChenUpsilon8ProductPan':['currentChenUpsilon8ProductCoefficient_sum','currentChenUpsilon8_le_switched_prime_fibres_add_unitFibres','exists_currentChenUpsilon8_sameCoefficient_pan_majorant'],
'CurrentChenUpsilon9FiniteMean':['currentChenUpsilon9PrefixPrimeFibre','currentChenUpsilon9PrefixPrimeFibre_divisor_card','currentChenUpsilon9_prefix_sum_upperDivisorSum','currentChenUpsilon9_switchedPrimeFibre_card_le_upperDivisorSum_add_cap','currentChenUpsilon9SwitchedUpperDensity'],
'CurrentChenUpsilon9PanAggregate':['currentChenUpsilon9_primesInAPBelow_eq_zero_of_not_coprime','currentChenUpsilon9PanActive','currentChenUpsilon9PanActive_subset'],
'CurrentChenUpsilon8CoprimeGateBudget':['eventually_currentChenUpsilon8_abs_coprimeGateError_le_singularNormalization'],
'CurrentChenUpsilon8SourceErrorBudget':['currentChenUpsilon8_prefixProducts_card_le_panUpper','eventually_currentChenUpsilon8_sourceErrors_le_singularNormalization']}
complete=[]
for mod,names in complete_specs.items():
    p=root/'ImbalancedChen'/f'{mod}.lean';byname={d['name']:d for d in declarations(p.read_text())};assert set(names)<=set(byname)
    complete.append({'path':str(p.relative_to(root)),'sha256':sha(p),'complete_actual_public_API_declarations':[byname[n] for n in names]})
report['complete_public_project_API_source']=complete
report['evidence_correction']={'prior_owner_report_path':str(old.relative_to(root)),'prior_owner_report_sha256':sha(old),'prior_report_preserved':True,'reason':'Before handoff, source-author check corrected four literal API excerpt windows, including Active9 and Active_subset whose prior excerpts were mispositioned. Complete actual public API declarations are now attached. No Lean source, type, definition, proof, dependency, semantic claim or DAG changed.','supersedes_for_semantic_review':True}
p=out/'20261016-U8FiniteMean-owner-semantics-api-corrected.json'
with p.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
assert sha(source)==report['source_sha256']
print(json.dumps({'source_sha256':sha(source),'corrected_owner_report_path':str(p.relative_to(root)),'corrected_owner_report_sha256':sha(p),'old_evidence_preserved':True,'complete_public_API_count':sum(len(x['complete_actual_public_API_declarations']) for x in complete)},indent=2))