from pathlib import Path
import ast, datetime, difflib, hashlib, json, re

W=Path('/workspace'); P=W/'p1-complete-proof'
O=P/'static-mixed-k-one-resource-and-sums'
assert not O.exists()
source=W/'blue-member-build/ImbalancedChen/P2Winner9MixedKOneFiniteCollapse.lean'
before=source.read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(before)=='e79458c31bde5b3b27f2f57e49367ced31e3964dc214b641cfee3acace98f100'
parser=ast.parse(Path('/tmp/prepare_third_rounded_gap_stored_four.py').read_text())
nodes=[n for n in parser.body if isinstance(n,ast.FunctionDef) and n.name in ('mask','scan') or isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='RX' for t in n.targets)]
ns={'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),'existing-comment-aware-parser','exec'),ns)
commands=ns['scan'](before); byname={x['name']:x for x in commands}
assert len(commands)==8
degree=byname['fourExponent_degree']['header'].decode().split(':=')[0].replace('theorem fourExponent_degree (a b c d : Fin 9) :','∀ a b c d : Fin 9,').strip()
factor=byname['fourFactorial_kernel']['header'].decode().split(':=')[0].replace('theorem fourFactorial_kernel (a b c d : Fin 9) :','∀ a b c d : Fin 9,').strip()
certificate=('private theorem closed_four_labels :\n    ('+degree+') ∧\n    ('+factor+') := by\n  decide +kernel\n\n').encode()
F=P/'mixed-k-one-two-proof-fragments'
homogeneous=(F/'homogeneous_one.proof.lean').read_bytes().rstrip()
weighted=(F/'weighted_kernel_mixedNumerator.proof.lean').read_bytes()
fixes=[
 ('(∑ i : Fin 9, ∑ i : Fin 9, F i i)'.encode(),'(∑ a : Fin 9, ∑ b : Fin 9, F a b)'.encode()),
 ('(∑ i : Fin 9, ∑ i : Fin 9, ∑ i : Fin 9, F i i i)'.encode(),'(∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, F a b c)'.encode()),
 ('(∑ i : Fin 9, ∑ i : Fin 9, ∑ i : Fin 9, ∑ i : Fin 9, F i i i i)'.encode(),'(∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9, F a b c e)'.encode())]
for old,new in fixes:
 assert weighted.count(old)==1
 weighted=weighted.replace(old,new,1)
scale='''by
  rw [actualMixedExpectation_eq_factorial_sum]
  simp_rw [fourthMoment_kernel]
  have hU : (d.U : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.UPos)
  have hL : (d.L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.LPos)
  have hG : (gapTotal d.gaps : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt d.gapsPos)
  have hsum :
      (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
        (d.gaps a : ℝ) * (d.y b : ℝ) * (d.deviations j c : ℝ) *
          (d.deviations j e : ℝ) * (kernel a b c e : ℝ)) =
        (mixedNumerator d j 1 : ℝ) := by
    exact_mod_cast (weighted_kernel_mixedNumerator d j)
  have hterm (a b c e : Fin 9) :
      (gapVertices d a * yVertices d b *
        bVertices d j c * bVertices d j e) *
          ((kernel a b c e : ℝ) / ((12 : ℕ).factorial : ℝ)) =
      ((d.gaps a : ℝ) * (d.y b : ℝ) * (d.deviations j c : ℝ) *
        (d.deviations j e : ℝ) * (kernel a b c e : ℝ)) /
          ((d.U : ℝ) * (d.L : ℝ)^2 * ((12 : ℕ).factorial : ℝ)) := by
    simp only [gapVertices, yVertices, bVertices, div_eq_mul_inv,
      mul_inv_rev, inv_pow]
    ring
  simp_rw [hterm]
  simp_rw [← Finset.sum_div]
  rw [hsum]
  norm_num [Nat.factorial]
  field_simp [hU, hL, hG]
  <;> ring
'''.encode().rstrip()
bodies={
 'fourExponent_degree':b'by\n  exact closed_four_labels.1 a b c d',
 'fourFactorial_kernel':b'by\n  exact closed_four_labels.2 a b c d',
 'homogeneous_one':homogeneous,
 'weighted_kernel_mixedNumerator':weighted.rstrip(),
 'actualMixedExpectation_eq_candidate':scale,
}
replacements=[]
for name,newbody in bodies.items():
 x=byname[name]; start=x['assignment']+2
 m=re.match(rb'\s*by\b',before[start:]);assert m
 body_start=start+m.end()-2
 end=x['end']
 # Preserve the comments and separating whitespace preceding the next command.
 nxt=before.find(b'\n/--',body_start,end)
 if nxt>=0: end=nxt
 elif name=='actualMixedExpectation_eq_candidate':end=before.index(b'\n\nend\n',body_start)
 while before[end-1:end] in (b'\n',b'\r',b' '):end-=1
 replacements.append((body_start,end,newbody,name))
old='(12.factorial : ℝ)'.encode();new='((12 : ℕ).factorial : ℝ)'.encode()
assert before.count(old)==1
at=before.index(old);replacements.append((at,at+len(old),new,'fourthMoment_kernel_private_Nat_factorial_syntax'))
insert=byname['fourExponent_degree']['start']
# Insert the private closed certificate before the original public doc comment.
insert=before.rfind(b'/--',0,insert)
replacements.append((insert,insert,certificate,'new_private_closed_four_labels'))
after=before
for a,b,v,name in sorted(replacements,reverse=True):after=after[:a]+v+after[b:]
aftercmd=ns['scan'](after);am={x['name']:x for x in aftercmd}
assert len(aftercmd)==9
headers=[];defs=[]
for x in commands:
 y=am[x['name']];expected=x['header']
 if x['name']=='fourthMoment_kernel':expected=expected.replace(old,new)
 assert expected==y['header'],x['name']
 headers.append({'name':x['name'],'kind':x['kind'],'private':x['private'],'complete_before_raw_header':x['header'].decode(),'complete_after_raw_header':y['header'].decode(),'raw_exact':x['header']==y['header']})
 if x['kind']=='def':
  # The next theorem's added helper sits after the kernel command's proof-free value.
  end=before.find(b'\n/--',x['assignment']+2,x['end'])
  if end<0:end=x['end']
  raw=before[x['start']:end].rstrip()
  assert raw in after
  defs.append({'name':x['name'],'complete_raw_definition':raw.decode(),'sha256':sha(raw)})
reversed_source=after
# Reverse using exact candidate offsets from the forward edit map.
shift=0;edits=[]
for a,b,v,name in sorted(replacements):
 edits.append({'name':name,'original_start':a,'original_end_exclusive':b,'candidate_start':a+shift,'candidate_end_exclusive':a+shift+len(v),'before':before[a:b].decode(),'after':v.decode()})
 shift+=len(v)-(b-a)
for e in reversed(edits):
 a=e['candidate_start'];b=e['candidate_end_exclusive'];assert reversed_source[a:b].decode()==e['after']
 reversed_source=reversed_source[:a]+e['before'].encode()+reversed_source[b:]
assert reversed_source==before
O.mkdir();files=[]
def put(n,b):
 q=O/n;q.parent.mkdir(parents=True,exist_ok=True)
 with q.open('xb') as f:f.write(b)
 r={'path':n,'bytes':len(b),'sha256':sha(b)};files.append(r);return r
def putj(n,v):return put(n,(json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
pre=put('baseline.lean',before);post=put('candidate.lean',after)
put('candidate.patch',''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile='actual-e794-pre',tofile='finite-certificate-and-sum-normalization')).encode())
put('prepare_mixed_k_one_resource_and_sums.py',Path(__file__).read_bytes())
put('ACTUAL_ORIGINAL_FAILURE.log',(P/'modern-p1-build/incremental-six-root-after-source-repairs/failure-observation-0007/P2Winner9MixedKOneFiniteCollapse.failure.log').read_bytes())
for n in ('homogeneous_one.proof.lean','weighted_kernel_mixedNumerator.proof.lean','DERIVATION_AND_DEPENDENCIES.json','FILES_MANIFEST.json','numerical-appendix-177-189.tex'):
 put('support/'+n,(F/n).read_bytes())
putj('COMPLETE_HEADERS_DEFINITIONS_AND_EXACT_DELTA.json',{'complete_original_headers':headers,'complete_original_definitions':defs,'new_private_header':am['closed_four_labels']['header'].decode(),'edits':edits,'whole_reverse_exact':True,'original_command_count':8,'candidate_command_count':9,'all_seven_public_headers_raw_exact':True,'only_original_header_exception':'private fourthMoment_kernel: 12.factorial -> (12 : Nat).factorial; original syntax had no elaborated kernel type, no equality of unparsed types is claimed','weighted_support_generation_fix':[{'before':a.decode(),'after':b.decode()} for a,b in fixes]})
putj('SOURCE_SELECTION.json',{'schema':'mixed_k_one_finite_certificate_and_algebra_candidate_v1','preparer':'/root','status':'ISOLATED_UNCOMPILED_PENDING_NONAUTHOR_GATE_AND_SOLE_OWNER_VALIDATION','prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'module':'ImbalancedChen.P2Winner9MixedKOneFiniteCollapse','baseline':pre,'candidate':post,'all_original_definitions_imports_options_numeric_data_final_target_hypotheses_quantifiers_exact':True,'original_headers_raw_exact_except_private_Nat_factorial_syntax':True,'new_private_helpers':1,'changed_original_proof_bodies':list(bodies),'resource_strategy':'One closed finite conjunction for all four labels is proved by decide +kernel, with no 6561-way explicit proof term expansion. Existing public heads project the certificate. No native_decide, new algorithm, external checker or budget change. Actual resource success is unclaimed.','sum_strategy':'Unique nonzero coordinate bijection for degree1; fifteen kernel terms reduce to eleven original signed scalar moments via finite sum factorization and pointwise ring; exact measured normalization pulls original fixed denominators through finite sums.','difficulty_classification':'Observed API/finite-sum normalization and original proof-term memory; actual header 12.factorial parse error. No substantive mathematical gap identified; candidate untested.','syntax_exception':'private fourthMoment_kernel original 12.factorial restored as (12 : Nat).factorial; all original public targets untouched','new_hypotheses_M_Ready_target_bound_or_numeric_oracles':False,'Lean_Lake_kernel_stock_numeric_invocations':0,'live_main_Member_P6_cache_runtime_queue_or_existing_records_mutated':False,'bounded_reuse_lookup':'Prior readonly mixed-k-one diagnosis 10e28b5d: same preimage in known published helper; no known whole repaired post; support finite algebra snippets reused, generation binder error explicitly corrected','manuscript1106':'a988cba584d803ae2856a0de50efb582f4f3dd6a paper/release-20261106/en numerical-appendix.tex177-195, argument.tex1096-1106 exact simplex moments and signed polynomial assembly'})
putj('FILES_MANIFEST.json',{'schema':'mixed_k_one_isolated_candidate_files_v1','files':files.copy(),'manifest_excludes_itself':True,'old_records_unchanged':True})
for n in ('candidate.lean','SOURCE_SELECTION.json','FILES_MANIFEST.json'):print(n,sha((O/n).read_bytes()))
