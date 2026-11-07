import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,hashlib,importlib.util
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py';assert sha(parser_path)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914'
spec=importlib.util.spec_from_file_location('u8_trueli_readonly_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');std=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux');paths={};heads={};hashes={}
helper=out/'drafts/20261016-U8CoprimeGateBudget-owner-review.py';tree=ast.parse(helper.read_text());exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'locate','read','walk'}],type_ignores=[]),str(helper),'exec'))
parents=['ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget','ImbalancedChen.CurrentChenUpsilon9TrueLiMass'];union=set();records=[];seen_sets=[]
for name in parents:
    seen,missing,findings=walk(name);assert not missing and not findings;seen_sets.append(seen);union|=seen
    arpath=state/('audits/20261015T225351728783Z/receipt.json' if name==parents[0] else 'audits/20261015T201216595359Z/receipt.json');ar=json.loads(arpath.read_text());assert ar['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar['targets'][name]==hashes[name]
    records.append({'module':name,'sha256':hashes[name],'closure_nodes':len(seen),'owned_receipt':str(arpath.relative_to(root)),'owned_receipt_sha256':sha(arpath)})
delta=seen_sets[1]-seen_sets[0]
print(json.dumps({'status':'READ_ONLY_NEXT_SINGLE_LEAF_PLAN_NOT_AUTHORED','parents':records,'parent_union':len(union),'proposed_candidate_if_exact_these_imports':len(union)+1,'extra_project_brought_by_owned9TrueLi_vs_c4':sorted(n for n in delta if n.startswith('ImbalancedChen')),'extra_foreign_brought_by_owned9TrueLi_vs_c4':sorted(n for n in delta if not n.startswith('ImbalancedChen')),'new_leaf_relative_foreign_vs_parent_union':[],'new_source_written':False},indent=2))