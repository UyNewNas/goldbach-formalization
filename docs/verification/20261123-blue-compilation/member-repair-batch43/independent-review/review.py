from pathlib import Path
import collections,datetime,hashlib,json,re,shlex,subprocess,sys
sys.path.insert(0,'/workspace/blue-source-review-utils')
from comment_decls import mask_comments_and_strings
R=Path(__file__).resolve().parent.parent;B=Path('/workspace/blue-member-build')
number=int(R.name.removeprefix('blue-member-repair-batch'))
def sha(b):return hashlib.sha256(b).hexdigest()
def ident(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
def load(p):return json.loads(p.read_bytes())
def bound(p,e):
 got=ident(p);assert got['bytes']==e['bytes'] and got['sha256']==e['sha256'],p
 return got
def assignment(mask,start):
 # Ignore assignments within binders/defaults and top-level type-level lets.
 stack=[];pairs={')':'(',']':'[','}':'{','⟩':'⟨'};pending_let=0;i=start
 while i<len(mask):
  ch=mask[i]
  if ch in '([{⟨':stack.append(ch)
  elif ch in pairs:assert stack and stack.pop()==pairs[ch],(i,ch)
  elif not stack:
   if re.match(r'let(?:I|U)?\b',mask[i:]) and (i==0 or not(mask[i-1].isalnum() or mask[i-1]=='_')):
    pending_let+=1
   if mask.startswith(':=',i):
    if pending_let:pending_let-=1
    else:return i
  i+=1
 raise ValueError('No declaration-level proof assignment')
top_pat=re.compile(r'(?m)^(?:@\[[^\n]*\][ \t]*)?(?:(?:private|protected|noncomputable)\s+)?(?:theorem|lemma|def|abbrev|structure|inductive|instance|namespace|end|open|section|variable|set_option|noncomputable section)\b')
th_pat=re.compile(r'(?m)^(?:@\[[^\n]*\][ \t]*)?(?P<private>private\s+)?(?:theorem|lemma)\s+(?P<name>[^\s({:]+)')
def parse(t):
 mask=mask_comments_and_strings(t);tops=list(top_pat.finditer(mask));hs=[];proofs={};defs=[]
 for x in th_pat.finditer(mask):
  a=assignment(mask,x.end())+2;end=next((y.start() for y in tops if y.start()>a),len(t));h=t[x.start():a]
  hs.append(dict(name=x.group('name'),private=bool(x.group('private')),header=h,sha256=sha(h.encode())))
  proofs[x.group('name')]=(a,end,t[a:end])
 for i,x in enumerate(tops):
  if re.match(r'(?:noncomputable\s+)?(?:def|abbrev|structure|inductive)\b',mask[x.start():]):
   end=tops[i+1].start() if i+1<len(tops) else len(t)
   raw=t[x.start():end];defs.append(dict(raw=raw,sha256=sha(raw.encode())))
 return hs,proofs,defs
def normalize(args):
 out=[];i=0
 while i<len(args):
  if args[i]=='-D':out.append('-D'+args[i+1]);i+=2
  else:out.append(args[i]);i+=1
 return out
core=[ident(R/n) for n in ['FINAL_RELEASE.json','PUBLICATION_FILES.json','VALIDATION_RESULTS.json','SOURCE_SELECTION.json']]
release,manifest,val,selection=[load(Path(x['path'])) for x in core]
assert release['status']=='FINAL_RELEASE'
assert core[1]['sha256']==release['publication_files_sha256']
assert core[2]['sha256']==release['validation_results_sha256']
assert set(selection)==set(val['modules'])==set(release['environment_public_export_counts'])
packet=[bound(R/x['path'],x) for x in manifest['files']]
expected_changes={41:['tendsto_test_original_sourceRegion','tendsto_original_box_plus_residual'],
 42:['selected_first_three_ge_omega','selected_third_prime_rough'],
 43:['smallBin_subset_prime_box','weightedBinMass_le_prime_box'],
 45:['weighted_moving_last_interval'],46:[]}
purposes={41:'Actual original coarse T3 policy on positive cube: original Gamma-2e old level, firstStop/firstcube/thirdcube/rough activation, positive cutoff and complementary exact small-prime remainder remain. Only empty-set integral API and pointwise beta normalization change.',
 42:'Exact finite admitted-source stratification: third-prime coordinate2 and all first THREE coordinates remain rough-active, the last-coordinate smallness and signed reciprocal-prime weights remain. Only definitional Fin/Nat coordinate exposure changes.',
 43:'The same actual original source bin is dominated by the same target-deleted prime box: first THREE intervals stay[omega,19/96), last interval retains its slightly open upper endpoint; original prime logarithm moment and scalar a/k remain. Only Fin equality simplification and sum multiplication API change.',
 45:'Original uniform moving-prime interval estimate and weighted original bins: K precedes targets/caps/endpoints, original Even hypotheses, strict endpoints, target deletion and6K/logN error remain. Only trans_eq cancellation and explicit unchanged additive summand API change.',
 46:'Exactly original Y11 registered source: fixed target2 is a positive upper carrier only above prime3; original target-deleted carrier remains on the left. Uniform exponent-window K precedes N,a,b,lo,hi; original3≤N^a condition and error b*K/(a²logN) remain. No source byte changes.'}
modules=[];sources=[]
for module,sel in selection.items():
 name=module.split('.')[-1];folder=R/name
 pre=(folder/'baseline.lean').read_bytes();post=(folder/'candidate.lean').read_bytes()
 assert sha(pre)==sel['preimage_sha256'];assert sha(post)==sel['postimage_sha256']==val['modules'][module]
 t0,t1=pre.decode(),post.decode();h0,p0,defs0=parse(t0);h1,p1,defs1=parse(t1)
 assert h0==h1 and defs0==defs1
 assert set(p0)==set(p1)
 changed=[n for n in p0 if p0[n][2]!=p1[n][2]];assert changed==expected_changes[number],changed
 def stripped(t,p):
  for k in sorted(changed,key=lambda k:p[k][0],reverse=True):
   a,e,_=p[k];t=t[:a]+' <TACTIC-BODY '+k+'> '+t[e:]
  return t
 assert stripped(t0,p0)==stripped(t1,p1)
 if number==46:
  assert pre==post
  registered=sel['registered_selected_source'];blob=subprocess.check_output(['git','-C','/workspace/goldbach-formalization','cat-file','blob',registered['git_blob_sha1']]);assert blob==post
 for root in [B,Path('/workspace/goldbach-formalization')]:
  item=ident(root/'ImbalancedChen'/(name+'.lean'));assert item['sha256']==sha(post);sources.append(item)
 before=folder/'before-build.log'
 if number!=46:
  raw=before.read_text();assert name in raw and 'error:' in raw
 else:assert (folder/'candidate.patch').read_bytes()==b''
 modules.append(dict(module=module,baseline_sha256=sha(pre),postimage_sha256=sha(post),
  complete_comment_aware_headers=h0,raw_definition_data_commands=defs0,changed_proofs=changed,
  all_complete_headers_and_raw_definitions_data_parameters_unchanged=True,
  all_bytes_outside_changed_proof_bodies_exact=True,all_imports_constants_hypotheses_domains_quantifiers_unchanged=True,
  raw_line_endings=dict(pre_CRLF=pre.count(b'\r\n'),post_CRLF=post.count(b'\r\n'),pre_bare_LF=pre.count(b'\n')-pre.count(b'\r\n'),post_bare_LF=post.count(b'\n')-post.count(b'\r\n')),
  mathematical_scope=purposes[number],header_or_definition_syntax_exceptions=[],new_mathematical_assumptions_or_weakened_statements=False,
  raw_original_failure=ident(before) if before.exists() else None,
  original_registered_source_byte_exact=number==46))
outputs=[]
for module,parts in val['source_plus_five_outputs'].items():
 assert len(parts)==6
 outputs += [bound(B/p,e) for p,e in parts.items()]
 assert parts['ImbalancedChen/'+module.split('.')[-1]+'.lean']['sha256']==val['modules'][module]
commands=val['normal_commands']+val['kernel_commands']+[val['audit_command']]
assert len(commands)==2*len(selection)+1 and all(c['exit_code']==0 for c in commands)
for c in commands:
 assert sha((R/c['log']).read_bytes())==c['log_sha256'];assert c['cwd']==str(B)
 assert c['argv'][:4]==['python3','/workspace/blue-build-tools/run_guarded.py','--state','/workspace/blue-build-tools/member-runtime-evidence/state.json']
reused_normal=None
if number==46:
 c=val['normal_commands'][0];op=Path(c['original_command_receipt']);original=load(op)
 assert original['exit_code']==0 and original['normal_build_passed']
 assert original['command']==c['argv'] and original['log_sha256']==c['log_sha256']
 assert all(original[k]==c[k] for k in ['started_utc','finished_utc','elapsed_seconds'])
 assert sha((op.parent/original['log']).read_bytes())==c['log_sha256']
 reused_normal=dict(original_command=ident(op),original_log=ident(op.parent/original['log']),same_single_normal_invocation=True,no_repeat_normal_claim=True)
runtime=load(R/'ACTUAL_RUNTIME_COMMANDS.json')
assert len(runtime['actual_compiler_commands'])==len(selection)+1
for path,event in runtime['actual_compiler_commands'].items():
 assert event['cwd']==str(B) and event['tool']=='lean'
 assert event['sysroot']=='/workspace/blue-build-tools/member-runtime/p0-ci-shadow-toolchain'
 assert event['command'][:4]==[event['sysroot']+'/bin/lean-runtime','-t0','-j2','-M12288']
 assert normalize(event['command'][4:])==normalize(event['input_args'])
 assert path in event['input_args']
 assert '-DmaxRecDepth=100000' in event['input_args'] and '-DmaxHeartbeats=4000000' in event['input_args']
 if path==str(R/'PublicAudit.lean'):assert event['input_args']==val['audit_command']['argv'][7:]
 else:
  assert 'ImbalancedChen.'+Path(path).stem in selection
  trace=load(B/('.lake/build/lib/lean/ImbalancedChen/'+Path(path).stem+'.trace'))
  lines=[x['message'] for x in trace['log'] if x['message'].startswith('.> LEAN_PATH=')];assert len(lines)==1
  tokens=shlex.split(lines[0][3:]);at=tokens.index(event['sysroot']+'/bin/lean')
  assert tokens[at+1:]==event['input_args']
exports=load(R/'PUBLIC_EXPORTS.json');log=(R/'types-axioms.log').read_text()
records=[json.loads(l.split('AUDIT_RECORD ',1)[1]) for l in log.splitlines() if 'AUDIT_RECORD ' in l]
assert len(records)==len(exports)==val['total_public_exports']==release['total_public_exports']
assert records==[{k:v for k,v in x.items() if k!='transitive_axioms'} for x in exports]
assert len({x['name'] for x in exports})==len(exports)
counts=dict(collections.Counter(x['module'] for x in exports));assert counts==val['public_export_counts']==release['environment_public_export_counts']
assert all(not x['is_axiom_declaration'] and '...' not in x['type_expression'] and 'sorryAx' not in x['type_expression'] for x in exports)
ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);noax=re.findall(r"'([^']+)' does not depend on any axioms",log)
assert len(ax)+len(noax)==len(exports)
am={n:{re.sub(r'\.\{[^}]*\}$','',s.strip()) for s in a.split(',')} for n,a in ax};am.update({n:set() for n in noax})
assert all(set(x['transitive_axioms'])==am[x['name']] for x in exports)
assert all(a<={'propext','Classical.choice','Quot.sound'} for a in am.values())
audit=(R/'PublicAudit.lean').read_text()
assert all(s in audit for s in ['env.constants.fold','env.getModuleIdxFor? name','!isPrivateName name','set_option pp.all true'])
assert 'AUDIT_FINISHED '+str(len(exports)) in log
for item in core+packet+sources+outputs:assert ident(Path(item['path']))==item
report=dict(schema='independent_P1_single_batch_complete_source_and_validation_review_v1',batch=number,status='PASS_INDEPENDENT_REVIEW',
 reviewer='/root/retained_reuse',reviewed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 source_review=modules,final_release_inputs=core,original_manifest_file_count=len(packet),
 all_recorded_original_manifest_file_sha256_and_sizes_match_and_stable=True,
 current_source_main_Member_match=sources,current_source_plus_five_facets=outputs,
 existing_validation=dict(actual_environment_public_counts=counts,total=len(exports),normal_exit_codes=[c['exit_code'] for c in val['normal_commands']],kernel_exit_codes=[c['exit_code'] for c in val['kernel_commands']],audit_exit_code=val['audit_command']['exit_code'],
  full_AST_records_equal_raw_log=True,canonical_owner_enumeration=True,no_type_elisions=True,transitive_axioms_equal_raw_print_records=True,
  only_standard_axioms=['propext','Classical.choice','Quot.sound'],actual_guard_trace_argv_cwd_sysroot_and_effective_flags_bound=True,
  source_plus5_facets_current_and_recorded_stable=True,reused_normal_invocation_binding=reused_normal),
 findings=[],Lean_kernel_type_axiom_build_calls_by_reviewer=0,actual_source_or_original_manifest_log_edits=0,
 limitations=['Acceptance is for SOURCE_SELECTION actual module keys and their recorded Member import/runtime context only.',
  'These are already verified necessary suppliers of the selected twenty-module P1 chain, not the complete manuscript/repository P1 proof.',
  'Original hypotheses, positive-cutoff domains, actual source objects, endpoints and uniform quantifier order remain; no new small-prime asymptotic or full-source theorem is inferred.',
  'No kernel-type equivalence claim is made for the old failing source before repair.'],
 late_addendum_handoff='Publish this independent review and its separate manifest as new late files; preserve original FINAL_RELEASE/PUBLICATION_FILES/VALIDATION_RESULTS, original sources and raw logs.')
out=R/'INDEPENDENT_REVIEW.json';assert not out.exists();out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
addition=dict(schema='independent_P1_review_separate_late_manifest_v1',batch=number,original_final_release=core[0],original_publication_manifest=core[1],
 new_files=[ident(out),ident(Path(__file__))],original_packet_edited=False)
late=R/'INDEPENDENT_REVIEW_FILES.json';assert not late.exists();late.write_text(json.dumps(addition,indent=2)+'\n')
print(json.dumps(dict(batch=number,review=ident(out),late_manifest=ident(late),full_source_headers=sum(len(m['complete_comment_aware_headers']) for m in modules),raw_defs=sum(len(m['raw_definition_data_commands']) for m in modules),actual_public=len(exports)),indent=2))
