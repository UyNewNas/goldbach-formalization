import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,hashlib,importlib.util
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pp=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py';assert sha(pp)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914';spec=importlib.util.spec_from_file_location('u8_harmonic_next_plan_parser',pp);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');std=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux');paths={};heads={};hashes={}
wp=out/'drafts/20261016-U8CoprimeGateBudget-owner-review.py';tree=ast.parse(wp.read_text());exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'locate','read','walk'}],type_ignores=[]),str(wp),'exec'))
parents=['ImbalancedChen.CurrentChenUpsilon8TrueLiMass','ImbalancedChen.CurrentChenUpsilon9HarmonicMean'];sets=[];records=[]
for name in parents:
    seen,missing,findings=walk(name);assert not missing and not findings;sets.append(seen);records.append({'module':name,'source_sha256':hashes[name],'resolved':len(seen)})
assert records[0]['source_sha256']=='9f009161174abeb734c21154ebc368a9ae3354b157fc2da42e199e76d307554c' and records[1]['source_sha256']=='1e50dc27e37d79eccd1b6cd3974963d78ebca651c369e85e2f524b6126d7cc35'
auditpath=state/'audits/20261015T203514598065Z/receipt.json';ar=json.loads(auditpath.read_text());assert ar['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar['targets'][parents[1]]==hashes[parents[1]]
obj=state/'lib/lean/ImbalancedChen/CurrentChenUpsilon9HarmonicMean.olean';assert sha(obj)==ar['inputs_before']['owned_object_parts'][parents[1]]['.olean']
union=sets[0]|sets[1];delta=sets[1]-sets[0]
print(json.dumps({'status':'READ_ONLY_PROPOSED_HARMONIC_VS_DENSITY_NO_NEW_SOURCE','parents':records,'parent_union':len(union),'candidate_if_exact_two_imports':len(union)+1,'extra_project_from_owned9Harmonic_vs_9f':sorted(n for n in delta if n.startswith('ImbalancedChen.')),'extra_foreign_from_owned9Harmonic_vs_9f':sorted(n for n in delta if not n.startswith('ImbalancedChen.')),'new_foreign_vs_parent_union':[],'owned9Harmonic_receipt':str(auditpath.relative_to(root)),'owned9Harmonic_receipt_sha256':sha(auditpath),'owned9Harmonic_declarations':ar['declaration_counts'][parents[1]],'TrueLi9f_actual_strict_owned_still_independent_gate':True,'source_written':False},indent=2))