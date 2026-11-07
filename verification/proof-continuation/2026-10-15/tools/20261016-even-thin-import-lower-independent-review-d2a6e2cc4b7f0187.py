import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,hashlib,json,re,subprocess,importlib.util
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');out=root/'.lake/proof-continuation/source-reviews';state=out.parent
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py'
tree=ast.parse(helper.read_text());wanted={'sha','uncomment','imports','assignment_at_top','declarations'}
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in wanted],type_ignores=[]),str(helper),'exec'))
module='ImbalancedChen.ActualRosserEvenBox';p=root/'ImbalancedChen/ActualRosserEvenBox.lean'
oldp=out/'drafts/ActualRosserEvenBox.55287bfc6e22bfe8bb7f5d00a8698f4030c4c1cea23468c4edb72bea30a2bf52.lean'
ownerp=out/'20261016-even-thin-boundary-import-root-author-scope.json'
assert sha(ownerp)=='0e70d4b3aa4e0c7a539b8a0ce2199270d7eb1fc6a910be230f3fb472256360bd'
owner=json.loads(ownerp.read_text());old=oldp.read_bytes();new=p.read_bytes()
assert sha(oldp)==owner['old_sha256']=='55287bfc6e22bfe8bb7f5d00a8698f4030c4c1cea23468c4edb72bea30a2bf52'
assert sha(p)==owner['new_sha256']=='8fa0519aaf72041f2178911edd13ef7ae8f5d18cbb1d0bc2eaf1a2599f94e31d'
x=old;patches=[]
for e in owner['edits']:
 a=e['old'].encode();b=e['new'].encode();assert x.count(a)==1;x=x.replace(a,b,1);patches.append(dict(e,occurrences=1))
assert x==new
x=new
for e in reversed(owner['edits']):
 a=e['old'].encode();b=e['new'].encode();assert x.count(b)==1;x=x.replace(b,a,1)
assert x==old and b'\r' not in new and b'\r' not in old
olds=declarations(old.decode());news=declarations(new.decode())
assert len(olds)==len(news)==9 and sum(d['kind']=='def' for d in news)==2
assert sum(d['complete_source_header']!=e['complete_source_header'] for d,e in zip(olds,news))==1
for d,e in zip(olds,news):
 assert (d['name'],d['kind'],d['private'])==(e['name'],e['kind'],e['private'])
 if d['kind']=='def':assert d['complete_definition']==e['complete_definition']
 else:assert d['complete_proof_body_after_by']==e['complete_proof_body_after_by']
assert '(k := k)) (T : Set (Fin (2 * k + 2) → ℕ))' in next(d['complete_source_header'] for d in news if d['name']=='actualRosserEvenBoundaryMap_injOn_strictAnti')
parserp=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py'
assert sha(parserp)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914'
spec=importlib.util.spec_from_file_location('lower_even_thin_fixed_parser',parserp);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
def project_graph(override):
 local={};foreign=set();missing=[]
 def visit(n):
  if not n.startswith('ImbalancedChen.'):
   foreign.add(n);return
  if n in local:return
  q=root/(n.replace('.','/')+'.lean')
  if not q.is_file():missing.append(n);return
  b=override if n==module else q.read_bytes();h=parser.header_imports(b.decode());assert not h['parser_findings']
  local[n]={'sha256':hashlib.sha256(b).hexdigest(),'header':h}
  for i in h['imports']:visit(i['module'])
 visit(module);assert not missing;return local,foreign
og,of=project_graph(old);ng,nf=project_graph(new)
assert len(og)==64 and len(ng)==55 and set(ng)-set(og)==set() and not nf-of
for n in set(og)&set(ng)-{module}:assert og[n]==ng[n]
for key,names in [('removed_local',sorted(set(og)-set(ng))),('removed_foreign_roots',sorted(of-nf))]:assert owner['relative_project_header_DAG'][key]==names
assert owner['relative_project_header_DAG']['current_local']==ng
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']};assert pins==owner['pins']
for n,h in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/n)==h
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');provider_checks=[]
for name in ['goldbach','mathlib']:
 q=providers/name;head=subprocess.check_output(['git','-C',str(q),'rev-parse','HEAD'],text=True).strip();expected=next(x['rev'] for x in packages if x['name']==name);diff=subprocess.run(['git','-C',str(q),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
 assert head==expected and diff.returncode==0;provider_checks.append({'name':name,'manifest_pin':expected,'actual_HEAD':head,'tracked_diff_HEAD_exit_code':diff.returncode})
api_specs=[
(root/'ImbalancedChen/ActualSmallRosser.lean',39,59,'Exact target-deleted small prime carrier and removal of enumeration cap only under actual cutoff<=cap'),
(root/'ImbalancedChen/FinitePrimeGeometryCore.lean',157,171,'Actual prime tuples: prime, target exclusion, inclusive lower and strict upper endpoints'),
(root/'ImbalancedChen/ActualPrimeBoxMass.lean',71,82,'StrictAnti from inclusive-lower/strict-upper separated adjacent actual boxes, including equal wall exponents'),
(root/'ImbalancedChen/ActualLowerRosserBoundaryExpansion.lean',118,121,'The sole expanded alias has exactly the explicit current conclusion, same strict least-prime filter and Nat.ceil level'),
(providers/'goldbach/MathlibNt/SieveTheory/LiLiuPrereqWFSmallRosser.lean',1,15,'Existing import route to public LinearSieve API without the dropped analytic project chain'),
(providers/'goldbach/MathlibNt/SieveTheory/LinearSieve.lean',1,8,'Existing direct public RosserChains import'),
(providers/'goldbach/MathlibNt/SieveTheory/LinearSieve/RosserChains.lean',183,216,'Exact lower chain parity, strict prefix and closed terminal tests; sorted-chain equivalence with qnot, qprime and qmin')]
apis=[{'path':str(q),'sha256':sha(q),'lines':[lo,hi],'role':role,'literal_source':'\n'.join(q.read_text().splitlines()[lo-1:hi])} for q,lo,hi,role in api_specs]
for rel,detail in owner['fixed_native_API'].items():assert sha(providers/'goldbach'/rel)==detail['sha256']
runp=state/'runs/20261015T222112982093Z-ImbalancedChen.ActualRosserEvenBox/receipt.json';receipt=json.loads(runp.read_text());logp=runp.with_name('stdout.log');log=logp.read_text()
assert receipt['status']=='FAILED' and receipt['binding']['source_sha256']==sha(oldp) and receipt['binding_after']['source_sha256']==sha(oldp)
assert receipt['binding']['pins']==receipt['binding_after']['pins']==pins
assert 'memory_exception' in log and 'excessive memory' in log
oldreport=out/'20261016-ActualRosserEvenBox-lower-independent-semantics.json'
forbidden=[]
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
 forbidden += [m.group(0) for m in re.finditer(pat,uncomment(new.decode()))]
assert not forbidden
claims=[
'All nine complete declarations, both definition bodies and seven proof bodies have been independently read. The old/new literal patches reconstruct in both directions exactly. Every proof and definition body is unchanged; the only changed public header delta-expands the literal actualLowerRosserBoundarySets definition. This is a definitionally identical finite conclusion, not a weakened boundary predicate.',
'Tail membership is the actual image of the first 2*k+1 coordinates. StrictAnti gives true injectivity: tail cardinality is exactly 2*k+1, weighted tail product has no multiplicities, equal boundary-map images recover the entire actual ordered tuple from its range, and equal tails force equal k. The injOn header includes the complete named argument (k := k).',
'The main input is the actual prime-box carrier. It supplies primality, p not dividing the same N, inclusive N^a<=p and strict p<N^b. Adjacent b_succ<=a_castSucc yields strict tuple decrease even when the adjacent exponents coincide. The cap hypothesis N^u<=cap removes only enumeration truncation and preserves p<cap and p<N^u.',
'The real-to-natural chain uses exactly ceil(N^beta). A nonempty tail and strict upper endpoints give tailprod<N^beta. Actual positive primes allow strict odd-index cube-prefix tests; zero-based not-Even indices in the native chain match the stated Odd indices. Inclusive lower endpoints and hshell give N^beta<=tailprod*q^3. Nat.lt_ceil and Nat.ceil_le are used in the correct strict/closed directions.',
'The terminal q is prime, not in the tail, and strictly less than all its elements by actual tuple injectivity and order. The native sorted-chain equivalence receives qnot, qprime and qmin, not an assumed boundary conclusion. Actual membership in the strict q<r powerset carrier is paid separately, retaining target exclusions and the literal cutoff.',
'The k=0 case is a genuine two-prime box with one-element tail, so total product strictness is valid and its internal odd-index condition is vacuous. No spurious empty-tail or zero-rank exception is introduced. Arbitrary natural N<=1 is excluded by the existing hN, as needed for real exponent monotonicity.',
'No hLower/hUpper, current main-term/density estimate, distribution statement, boundary supplier, analytic mean or core sieve inequality occurs as a caller premise. The main conclusion places genuine finite boxes into the lower Rosser boundary with exact ranks; it is not itself a density lower bound or closure of the complete current theorem.',
'The direct import reduction removes nine existing project modules and three foreign fringe roots from the bounded project source graph, adds none, and preserves fixed providers and pins. This is import/source evidence only; native full foreign closure objects, serialization, cache acceptance and kernel replay have not been checked in this review.',
'The old5528 runtime receipt remains FAILED with only an interpreter memory_exception. No OOM site has been inferred. The new8fa source has not been compiled by this reviewer; reduced imports neither guarantee memory fit nor imply strict or owned success.'
]
review={'status':'SOURCE_ONLY_NONAUTHOR_COMPLETE_TYPES_DEFINITIONS_PROOFS_AND_THIN_IMPORT_REVIEW','reviewer':'/root/lower_resume (non-author)','created_utc':datetime.now(timezone.utc).isoformat(),'module':module,'old_source_sha256':sha(oldp),'current_source_sha256':sha(p),'root_owner_report':{'path':str(ownerp),'sha256':sha(ownerp)},'old_snapshot':{'path':str(oldp),'sha256':sha(oldp)},'full_current_source':new.decode(),'complete_declarations':news,'declaration_count':9,'definition_count':2,'proof_count':7,'theorem_separator':'actual := by, not the first named-argument :=','all_proof_and_definition_bodies_unchanged':True,'other_eight_headers_unchanged':True,'sole_main_header_delta_is_exact_alias_expansion':True,'literal_byte_patches':patches,'forward_bytes_exact':True,'inverse_bytes_exact':True,'LF_preserved':True,'independent_mathematical_findings':[],'mathematical_review':claims,'fixed_APIs':apis,'direct_parents':[{'module':n,'source_sha256':ng[n]['sha256'],'header':ng[n]['header']} for n in ['ImbalancedChen.ActualSmallRosser','ImbalancedChen.ActualPrimeBoxMass']],'independent_relative_project_DAG':{'parser_path':str(parserp),'parser_sha256':sha(parserp),'old_project_count':len(og),'current_project_count':len(ng),'removed_local':sorted(set(og)-set(ng)),'added_local':sorted(set(ng)-set(og)),'foreign_fringe_added':sorted(nf-of),'foreign_fringe_removed':sorted(of-nf),'current_local':ng,'scope':'project sources and foreign fringe only, no full foreign closure or kernel/cache acceptance'},'pins':pins,'provider_HEAD_and_tracked_clean_checks':provider_checks,'prior_failure':{'receipt_path':str(runp),'receipt_sha256':sha(runp),'stdout_path':str(logp),'stdout_sha256':sha(logp),'status':receipt['status'],'actual_stdout':log,'source_old_still_FAILED':True},'metadata_supersession':{'historical_report_path':str(oldreport),'historical_report_sha256':sha(oldreport),'old_report_preserved_unchanged':True,'supersedes':'Only the old first-:= metadata extraction of the injOn named-argument header. This new report includes all complete headers using actual := by; historical old source and failed runtime facts are retained.'},'forbidden_placeholder_option_matches':forbidden,'no_Lean_build_install_or_source_edit_performed':True,'bytecode_writes_disabled':True,'no_strict_owned_or_cache_acceptance_claimed':True,'runtime_boundary':'New exact8fa source remains subject to root gate and sole runtime owner real strict/full-owned checks; old OOM evidence is preserved.'}
reportp=out/'20261016-ActualRosserEvenBox-thin-import-lower-independent-review.json'
assert not reportp.exists();reportp.write_text(json.dumps(review,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
assert sha(p)==owner['new_sha256'] and sha(ownerp)=='0e70d4b3aa4e0c7a539b8a0ce2199270d7eb1fc6a910be230f3fb472256360bd'
print(json.dumps({'report':str(reportp),'sha256':sha(reportp),'source':sha(p),'declarations':len(news),'defs':2,'proofs':7,'project_DAG':[len(og),len(ng)],'addedforeign':sorted(nf-of),'parent_hashes':{n:ng[n]['sha256'] for n in ['ImbalancedChen.ActualSmallRosser','ImbalancedChen.ActualPrimeBoxMass']},'providers':provider_checks,'status':'SOURCE_ONLY'},ensure_ascii=False,indent=2))