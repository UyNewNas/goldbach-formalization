from pathlib import Path
import ast,datetime,difflib,hashlib,json,re
W=Path('/workspace');P=W/'p1-complete-proof';O=P/'static-mixed-k-one-sum-factorization-v2'
assert not O.exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
src=W/'blue-member-build/ImbalancedChen/P2Winner9MixedKOneFiniteCollapse.lean';before=src.read_bytes()
assert sha(before)=='e88f3f62d3b7fee4af218b9f372aae3b6443dc604e57ef377a934b199f2b9aab'
after=before;edits=[]
for args in [('a','b'),('a','b','c'),('a','b','c','e')]:
 old='    simp only [Finset.sum_mul, Finset.mul_sum]\n'
 for var in args:old+='    apply Finset.sum_congr rfl\n    intro '+var+' h'+var+'\n'
 old+='    exact hp '+' '.join(args)+'\n'
 new='    simp_rw [hp]\n    simp only [← Finset.mul_sum, ← Finset.sum_mul]\n'
 assert after.count(old.encode())==1
 edits.append({'before':old,'after':new,'local_helper':'sep'+str(len(args))})
 after=after.replace(old.encode(),new.encode(),1)
rev=after
for x in reversed(edits):
 # All three replacements intentionally share one body; reverse by ordered occurrences.
 pass
parts=after.split(edits[0]['after'].encode());assert len(parts)==4
rev=parts[0]
for i,x in enumerate(edits):rev+=x['before'].encode()+parts[i+1]
assert rev==before
t=ast.parse(Path('/tmp/prepare_third_rounded_gap_stored_four.py').read_text())
nodes=[n for n in t.body if isinstance(n,ast.FunctionDef)and n.name in ('mask','scan')or isinstance(n,ast.Assign)and any(isinstance(z,ast.Name)and z.id=='RX'for z in n.targets)]
ns={'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),'existing-comment-aware-parser','exec'),ns)
a=ns['scan'](before);b=ns['scan'](after);heads=[];defs=[];changed=[]
for x,y in zip(a,b,strict=True):
 assert (x['name'],x['kind'],x['private'],x['header'])==(y['name'],y['kind'],y['private'],y['header'])
 heads.append({'name':x['name'],'kind':x['kind'],'private':x['private'],'complete_raw_header':x['header'].decode(),'sha256':sha(x['header'])})
 xb=before[x['assignment']+2:x['end']];yb=after[y['assignment']+2:y['end']]
 if x['kind']=='def':
  assert xb==yb;raw=before[x['start']:x['end']];defs.append({'name':x['name'],'complete_raw_region':raw.decode(),'sha256':sha(raw)})
 elif xb!=yb:changed.append(x['name'])
assert len(heads)==9 and len(defs)==2 and changed==['weighted_kernel_mixedNumerator']
D=W/'blue-member-repair-batch98';log=(D/'P2Winner9MixedKOneFiniteCollapse-normal.log').read_bytes();cmdraw=(D/'P2Winner9MixedKOneFiniteCollapse-normal-command.json').read_bytes();cmd=json.loads(cmdraw)
assert (len(log),sha(log))==(8466,'abf8c55fc60a7134cd12fe455ca24d7e3e18a199bd0395be16da59e507ec83c0')
assert cmd['exit_code']==1 and cmd['log_sha256']==sha(log)
assert re.findall(rb'(?m)^error: ImbalancedChen/P2Winner9MixedKOneFiniteCollapse\.lean:(\d+):',log)==[b'160',b'172',b'186']
prior=P/'static-mixed-k-one-resource-and-sums';review=(prior/'INDEPENDENT_REVIEW.json')
if not review.exists():review=prior/'INDEPENDENT_STATIC_REVIEW.json'
if not review.exists():review=next(x for x in prior.glob('*REVIEW.json')if 'FILES'not in x.name)
pr=review.read_bytes();assert sha(pr)=='853c7492fb216f42d1378946b0c708491d9c3a87fdd5b8a9da82584ac4826f22'
O.mkdir();files=[]
def put(n,b):
 p=O/n;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb')as f:f.write(b)
 r={'path':n,'bytes':len(b),'sha256':sha(b)};files.append(r);return r
def putj(n,v):return put(n,(json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
pre=put('baseline.lean',before);post=put('candidate.lean',after)
put('candidate.patch',''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile='actual-e88f-failed',tofile='factor-pull-v2')).encode())
put('ACTUAL_V1_NORMAL_FAILURE.log',log);put('ACTUAL_V1_NORMAL_COMMAND.json',cmdraw)
put('prior-evidence/V1_NONAUTHOR_STATIC_REVIEW.json',pr)
put('prepare_mixed_k_one_sum_factorization_v2.py',Path(__file__).read_bytes())
putj('COMPLETE_HEADERS_DEFINITIONS_AND_EXACT_DELTA.json',{'full_headers':heads,'complete_defs':defs,'only_changed_original_theorem':changed[0],'local_proof_fragments':edits,'whole_reverse_exact':True,'all_other_bytes_exact':True})
putj('SOURCE_SELECTION.json',{'schema':'mixed_k_one_sum_factor_pull_v2','preparer':'/root','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'ISOLATED_UNCOMPILED_PENDING_NONAUTHOR_GATE_AND_ORIGINAL_OWNER_VALIDATION','module':'ImbalancedChen.P2Winner9MixedKOneFiniteCollapse','baseline':pre,'candidate':post,'v1_nonauthor_review_sha256':sha(pr),'actual_normal':cmd,'root_cause':'Expanding all products of sums with sum_mul and mul_sum reverses the nested sum binder order on the RHS, yielding k*f(b)*g(a), etc. The actual errors are exactly hp argument permutations. Rewrite F pointwise using the original hp first, then pull constant factors from the nested sums using the inverse rules. This keeps the original variable order and avoids commutation by reindexing.','math_scope':'Original finite equality-partition kernel and degree-one convolution identity, 1106 numerical-appendix177–195 exact simplex moments; no new analytic lemma or hypothesis.','only_three_local_helper_proof_bodies_changed':True,'all9_headers_and_2defs_imports_options_data_final_target_and_other_proofs_raw_exact':True,'v1_closed_certificate_homogeneous_private12factorial_and_finalscale_retained':True,'absence_of_errors_in_other_v1_declarations_is_not_independent_kernel_acceptance':True,'Lean_Lake_kernel_stock_numeric_or_test_invocations':0,'live_main_Member_P6_cache_queue_or_existing_record_mutations':False,'actual_success_or_resource_outcome_claimed':False})
putj('FILES_MANIFEST.json',{'schema':'mixed_k_one_three_local_proof_fragments_v2_files','files':files.copy(),'old_records_unchanged':True,'manifest_excludes_itself':True})
for n in ('candidate.lean','SOURCE_SELECTION.json','FILES_MANIFEST.json'):print(n,sha((O/n).read_bytes()))
