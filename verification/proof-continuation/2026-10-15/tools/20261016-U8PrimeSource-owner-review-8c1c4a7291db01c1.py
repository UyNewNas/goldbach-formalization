import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re,datetime,importlib.util
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation'
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py'
spec=importlib.util.spec_from_file_location('frozen_header_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
sha=lambda b:hashlib.sha256(b).hexdigest()
module='ImbalancedChen.CurrentChenUpsilon8PrimeSource';src=root/'ImbalancedChen/CurrentChenUpsilon8PrimeSource.lean';source=src.read_bytes();text=source.decode()
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');std=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux')
paths={};heads={};hashes={}
def locate(name):
 if name not in paths:
  rel=Path(name.replace('.','/')).with_suffix('.lean'); candidates=[root/rel] if name=='ImbalancedChen' or name.startswith('ImbalancedChen.') else [providers/p['name']/rel for p in packages]+[std/'src/lean'/rel,std/'src/lean/lake'/rel]
  paths[name]=next((p for p in candidates if p.is_file()),None)
 return paths[name]
def read(name):
 if name not in heads:
  p=locate(name)
  if p is None:heads[name]=None
  else:
   b=p.read_bytes();hashes[name]=sha(b);heads[name]=parser.header_imports(b.decode())
 return heads[name]
def walk(name):
 seen=set();unresolved=[];findings=[]
 def visit(n):
  if n in seen:return
  seen.add(n);h=read(n)
  if h is None:unresolved.append(n);return
  if h['parser_findings']:findings.append({'module':n,'findings':h['parser_findings']})
  for e in h['imports']:visit(e['module'])
 visit(name);return seen,unresolved,findings
direct=list(dict.fromkeys(x['module'] for x in read(module)['imports'] if not x['implicit']));baseline=set()
for m in direct:baseline.update(walk(m)[0])
candidate,missing,findings=walk(module);assert not missing and not findings and candidate-baseline=={module}
code=parser.uncomment(text);forbidden=re.findall(r'(?m)^\s*(?:axiom|unsafe|opaque)\b|\b(?:sorry|admit|native_decide)\b|set_option\s+(?:linter|debug\.skipKernelTC|autoImplicit)',code);assert not forbidden
new=sorted(candidate-baseline);inventory=sorted((m,hashes.get(m)) for m in candidate)
common={'status':'SOURCE_ONLY_ADVISORY_REVIEW','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate':module,'source_sha256':sha(source),'no_compiler_invoked':True,'no_kernel_or_axiom_acceptance_claimed':True,'bytecode_writes_disabled':True}
dag=dict(common,header_parser_sha256=sha(parser_path.read_bytes()),method='Fresh full source closure using the pinned grammar, all manifest provider roots, Lean and Lake source roots, implicit Init, public/meta/import-all. Pure source graph; no object alignment or provider pin verification claimed.',direct_imports=direct,baseline_modules=[{'module':m,'source_sha256':hashes[m]} for m in direct],baseline_union_resolved=len(baseline),candidate_resolved=len(candidate),new_project_vs_union=[m for m in new if m.startswith('ImbalancedChen.')],new_foreign_vs_union=[m for m in new if not m.startswith('ImbalancedChen.')],candidate_unresolved=missing,parser_findings=findings,candidate_forbidden_source_commands=forbidden,closure_module_sha_inventory_sha256=sha(json.dumps(inventory).encode()))
out=state/'source-reviews/20261016-U8PrimeSource-proper-dag.json';out.write_text(json.dumps(dag,indent=2)+'\n')
headers=re.findall(r'(?m)^(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def)\s+[\s\S]*?(?=:=)',code);assert len(headers)==7
pan=providers/'goldbach/MathlibNt/SieveTheory/LiLiuPanBoundedAggregate.lean'
pans=pan.read_text();k=pans.index('theorem liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving');panheader=pans[k:pans.index(':=',k)]
sem=dict(common,reviewer='lower_resume self-review, not independent validation',declaration_count=len(headers),complete_declaration_headers=headers,findings=[],checked_semantics=[
'From literal eighth selector membership the actual second prime satisfies p2>=N^(1/3), so the real natural-cast cube identity gives p2^3>=N without an extra asymptotic assumption or an N lower-threshold hypothesis.',
'The original actual quotient witness is reused with arbitrary N,b=p1*p2,q. It pays actual b*q<N and q>0 before the composite contradiction; the imported theorem has no ninth-selector or ninth-cutoff hypothesis.',
'If q is composite and not one, its true prime minFac has minFac^2<=q. Actual original roughness at p2 gives p2<=minFac, hence p2^2<=q. Actual p1 is prime, so p1>1; thus N<=p2^3<p1*p2^3<=p1*p2*q<N, contradiction.',
'The new actual sigma PrimeTriples retains the complete outer pair label and filters only the actual quotient source by Nat.Prime. UnitFibres are the actual outer pairs with one in that same original source. No multiplicity is replaced by an indicator.',
'The explicit triple membership dictionary retains both original strict/inclusive bands, original moving sqrt(N/p1) selector wall, actual target prime N-p1*p2*q including its coprimality carrier, and the original inclusive roughness q>=p2.',
'The already proved general prime_mem_iff is reused at z=p2; no square-root quotient cutoff from the ninth source is imported into the eighth statement.',
'The actual row cardinality partitions the original finite source into prime quotients and the possible unit quotient, using the proved actual prime-or-unit result. Finite sigma cardinalities and exact sums then give current Upsilon8 = actual PrimeTriples.card + actual UnitFibres.card.',
'No generic Pan/finite count/density/harmonic wrappers are cloned. This leaf imports only the owned ninth source and reuses its two genuinely general finite arithmetic lemmas. No owned source changes.'],
future_Pan_scope_read_only_not_a_result={'provider':str(pan),'provider_source_sha256':sha(pan.read_bytes()),'full_declaration_header':panheader,'checked':'The actual existing theorem allows A2<=N^(2/3), with exists C,B,N0 before N/window/f and abs(f)<=1. This is inclusive 2/3, not a ninth .618 restriction.','not_yet_proved_in_this_leaf':['Actual eighth prefix product strict upper bound N^(2/3) and exact ceil endpoint A2<=N^(2/3).','Actual same modulus-independent zero-one coefficient with ordered-prime injection and support.','Actual finite count, coprime gate, signed Pan aggregate, unit/small-P errors and ordinary density factor.']},
remaining=['No Lean elaboration, kernel replay or owned-object acceptance claimed.','Independent full source review and exact first runtime authorization are separate.','No adopted K, ordinary eighth upper mean or full current hLower is asserted.'])
semout=state/'source-reviews/20261016-U8PrimeSource-semantics.json';semout.write_text(json.dumps(sem,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'source_sha256':sha(source),'declarations':len(headers),'dag':str(out.relative_to(root)),'dag_sha256':sha(out.read_bytes()),'semantics':str(semout.relative_to(root)),'semantics_sha256':sha(semout.read_bytes()),'candidate_count':len(candidate),'baseline_union_count':len(baseline),'new_modules':new}))
