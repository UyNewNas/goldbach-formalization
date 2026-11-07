import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,importlib.util
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
helper=out/'drafts/20261016-U8CoprimeGateBudget-owner-review.py';tree=ast.parse(helper.read_text())
source_helpers=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py';htree=ast.parse(source_helpers.read_text())
exec(compile(ast.Module(body=[n for n in htree.body if isinstance(n,ast.FunctionDef) and n.name=='sha'],type_ignores=[]),str(source_helpers),'exec'))
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py';assert sha(parser_path)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914'
spec=importlib.util.spec_from_file_location('u8_finite_plan_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');std=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux');paths={};heads={};hashes={}
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'locate','read','walk'}],type_ignores=[]),str(helper),'exec'))
parents=['ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget','ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget','ImbalancedChen.CurrentChenUpsilon9FiniteMean']
union=set();result=[]
for name in parents:
    seen,missing,findings=walk(name);assert not missing and not findings
    union|=seen
    result.append({'module':name,'sha256':hashes[name],'closure_nodes':len(seen)})
assert hashes[parents[0]]=='c4f5a801eadd6128f088b99cd8128602aeba1d0d8fa2a24906cd3e9cd387e761'
assert hashes[parents[1]]=='9d6cb563579a743fd2d5bdcbef19714391d221648ffa3c1bf7b6a2b483b2d52e'
print(json.dumps({'status':'READ_ONLY_PROPOSED_ONE_LEAF_PARENT_UNION','parents':result,'parent_union_nodes':len(union),'proposed_new_module':'ImbalancedChen.CurrentChenUpsilon8FiniteMean','proposed_direct_imports_only':parents,'proposed_nodes_if_no_additional_import':len(union)+1,'relative_new_local':['ImbalancedChen.CurrentChenUpsilon8FiniteMean'],'relative_new_foreign':[],'new_source_written':False,'missing':[],'parser_findings':[]},indent=2))