import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py'
ns=ast.parse(helper.read_text());wanted={'sha','uncomment','imports','assignment_at_top','declarations'}
exec(compile(ast.Module(body=[n for n in ns.body if isinstance(n,ast.FunctionDef) and n.name in wanted],type_ignores=[]),str(helper),'exec'))
p=root/'ImbalancedChen/CurrentChenUpsilon8SourceErrorBudget.lean'
old_report=out/'20261016-U8SourceErrorBudget-owner-semantics.json';assert sha(old_report)=='9fe600cac7b46b169b3a3cdd7b6eed7b092f5aba0bf3a40a16293d3a20f637e0'
old=json.loads(old_report.read_text())['full_current_source'].encode();new=p.read_bytes()
old_sha='f8a7e49a7e802d1dfc6459ee5ef0df4086f53e24b05464be05ffc59545aa7d29';new_sha='9d6cb563579a743fd2d5bdcbef19714391d221648ffa3c1bf7b6a2b483b2d52e'
assert hashlib.sha256(old).hexdigest()==old_sha and sha(p)==new_sha
anchor='    rw [currentChenUpsilon8_eq_largeGoldbachPrimeTriples_add_errors]\n'
insert='''    change
      (((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ)) / singularNormalization N =
        (currentChenUpsilon8 N -
          ((currentChenUpsilon8LargeGoldbachPrimeTriples N).card : ℝ)) / singularNormalization N
'''
assert old.count(anchor.encode())==1 and old.replace(anchor.encode(),(insert+anchor).encode())==new
assert new.count(insert.encode())==1 and new.replace(insert.encode(),b'')==old
old_ds=declarations(old.decode());new_ds=declarations(new.decode())
assert len(old_ds)==len(new_ds)==13 and sum(x['kind']=='def' for x in new_ds)==2
assert imports(old.decode())==imports(new.decode())==['ImbalancedChen.CurrentChenUpsilon8ProductPan']
changes=[]
for a,b in zip(old_ds,new_ds):
    assert (a['kind'],a['name'],a['private'],a['complete_source_header'])==(b['kind'],b['name'],b['private'],b['complete_source_header'])
    if a['kind']=='def':assert a['complete_definition']==b['complete_definition']
    elif a['complete_proof_body_after_by']!=b['complete_proof_body_after_by']:changes.append(a['name'])
assert changes==['tendsto_currentChenUpsilon8_sub_largeGoldbachPrimeTriples_normalized']
run=state/'runs/20261015T224355797493Z-ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget';receipt_path=run/'receipt.json';log_path=run/'stdout.log';receipt=json.loads(receipt_path.read_text());log=log_path.read_text()
assert receipt['status']=='FAILED' and receipt['exit_code']==1
assert receipt['binding']['source_sha256']==receipt['binding_after']['source_sha256']==old_sha
assert log.count('error:')==1 and ':210:8:' in log and 'Did not find an occurrence' in log and '(fun N =>' in log
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
assert pins==receipt['binding']['pins']==receipt['binding_after']['pins']
for name,value in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/name)==value
parent=root/'ImbalancedChen/CurrentChenUpsilon8ProductPan.lean';assert sha(parent)=='80621797c21adc263fc702e07a13c0b0b543a40f34ca2658a7fa281e1af12b11'==receipt['binding']['direct_source_sha256']['ImbalancedChen.CurrentChenUpsilon8ProductPan']
parent_object=state/'lib/lean/ImbalancedChen/CurrentChenUpsilon8ProductPan.olean';assert sha(parent_object)==receipt['binding']['dependencies']['ImbalancedChen.CurrentChenUpsilon8ProductPan']
parent_audit=state/'audits/20261015T215816603875Z/receipt.json';ar=json.loads(parent_audit.read_text());assert ar['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar['targets']['ImbalancedChen.CurrentChenUpsilon8ProductPan']==sha(parent)
manifest=json.loads((root/'lake-manifest.json').read_text());providers=Path('/home/slava/codex-lean-ve/native-packages');provider_checks=[]
for name in ['goldbach','mathlib']:
    pr=providers/name;expected=next(x['rev'] for x in manifest['packages'] if x['name']==name);actual=subprocess.check_output(['git','-C',str(pr),'rev-parse','HEAD'],text=True).strip();diff=subprocess.run(['git','-C',str(pr),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
    assert actual==expected and diff.returncode==0
    provider_checks.append({'name':name,'actual_HEAD':actual,'manifest_pin':expected,'git_diff_HEAD_tracked_exit_code':diff.returncode})
api_specs=[(providers/'mathlib/Mathlib/Order/Filter/Tendsto.lean',100,115,'Tendsto.congr prime transports the proved source-error limit along eventual pointwise equality'),(providers/'mathlib/Mathlib/Order/Filter/Basic.lean',647,654,'Eventually.of_forall accepts the actual pointwise goal; each function application is beta-definitionally equal to the explicit changed equality')]
apis=[{'path':str(q),'sha256':sha(q),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(q.read_text().splitlines()[lo-1:hi])} for q,lo,hi,role in api_specs]
forbidden=[]
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
    forbidden.extend(m.group(0) for m in re.finditer(pat,uncomment(new.decode())))
assert not forbidden
report={'status':'SOURCE_ONLY_AUTHOR_ACTUAL_DIAGNOSTIC_PROOF_REBIND_PENDING_NONAUTHOR_AND_RUNTIME','reviewer':'/root/lower_resume (source author)','created_at_utc':datetime.now(timezone.utc).isoformat(),'module':'ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget','source_path':str(p.relative_to(root)),'old_source_sha256':old_sha,'new_source_sha256':new_sha,'old_source_evidence':{'path':str(old_report.relative_to(root)),'sha256':sha(old_report),'method':'The archived full old source is hashed back to the exact actual failure source.'},'actual_diagnostic':{'receipt_path':str(receipt_path.relative_to(root)),'receipt_sha256':sha(receipt_path),'log_path':str(log_path.relative_to(root)),'log_sha256':sha(log_path),'full_stdout':log,'status':'FAILED','exit_code':receipt['exit_code'],'binding_before_equals_after':receipt['binding']==receipt['binding_after'],'sole_failure':'line210 rewrite cannot find currentChenUpsilon8 behind unreduced lambda applications','resource_command':receipt['command'],'lean_memory_mib':receipt['lean_memory_mib'],'rss_guard_mib':receipt['rss_guard']['limit_mib'],'guard_error':receipt['guard_error']},'literal_byte_patch':{'old':anchor,'new':insert+anchor,'occurrences':1,'forward_exact':True,'inverse_exact':True,'inverse_method':'Delete the unique inserted change block to reproduce all old bytes exactly.'},'declaration_count':13,'definition_count':2,'all_complete_new_headers_definitions_and_proofs':new_ds,'full_new_source':new.decode(),'invariant_checks':{'all_13_complete_headers_exactly_unchanged':True,'both_complete_definitions_exactly_unchanged':True,'imports_exactly_unchanged':True,'all_other_proof_bodies_exactly_unchanged':True,'one_modified_proof':changes,'all_thresholds_cutoffs_constants_domains_exactly_unchanged_by_inverse_bytes':True,'pins_exactly_unchanged':True,'no_resource_or_linter_change':True},'source_semantics':['The literal actual U8 prime-triple carriers and exact original large/small/unit partition are unchanged. All full finite counts and zero normalized error statements are unchanged.','The sole proof insertion explicitly changes the goal from two lambda applications at N to their beta-reduced scalar equality. No simplification lemma, algebraic estimate, premise, endpoint or source selector is added.','The existing exact literal-count partition then rewrites the now-visible RHS, and the existing ring proves the same equality. This is an attempted local proof/API repair guided by the actual diagnostic, not a claim that the new source elaborates.'],'fixed_API_source_evidence':apis,'parent':{'source_sha256':sha(parent),'actual_object_sha256':sha(parent_object),'owned_receipt_path':str(parent_audit.relative_to(root)),'owned_receipt_sha256':sha(parent_audit)},'same_import_DAG_rebind':{'parent_current_hash_matches_original_DAG':True,'old_owner_DAG_path':'.lake/proof-continuation/source-reviews/20261016-U8SourceErrorBudget-owner-proper-dag.json','old_owner_DAG_sha256':'327c60f57a0559878bcd8e41e5a3e9aff0ce7499439194ce827cfd37e119675a','delta_vs_owned806':{'only_new_local':'ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget','new_foreign':[]},'new_full_walk_claimed':False,'method':'Source imports and every original declaration type/definition are byte-identical; current parent source/object/pins are freshly bound. This is a proof-byte rebind, not a new full DAG walk.'},'pins':pins,'providers_current':provider_checks,'forbidden_hits':forbidden,'no_Lean_or_build_invoked':True,'bytecode_writes_disabled':True,'no_kernel_owned_or_cache_acceptance_claimed':True,'old_failed_evidence_preserved':True,'findings':[]}
report_path=out/'20261016-U8SourceErrorBudget-beta-repair-owner-rebind.json'
with report_path.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
assert sha(p)==new_sha
print(json.dumps({'source_sha256':new_sha,'report_path':str(report_path.relative_to(root)),'report_sha256':sha(report_path),'complete_declarations':13,'definitions':2,'forward_inverse_exact':True,'new_foreign':[]},indent=2))