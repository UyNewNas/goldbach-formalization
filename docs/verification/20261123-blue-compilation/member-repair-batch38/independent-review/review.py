from pathlib import Path
import collections,datetime,difflib,hashlib,json,re,shlex,sys
sys.path.insert(0,'/workspace/blue-source-review-utils')
from comment_decls import mask_comments_and_strings
from comment_decls_v2 import proof_assignment
R=Path('/workspace/blue-member-repair-batch38'); B=Path('/workspace/blue-member-build')
def sha(b):return hashlib.sha256(b).hexdigest()
def identity(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
def read(p):return json.loads(p.read_bytes())
def bound(p,e):
 got=identity(p);assert got['bytes']==e['bytes'] and got['sha256']==e['sha256'],p
 return got
core=[identity(R/n) for n in ['FINAL_RELEASE.json','PUBLICATION_FILES.json','VALIDATION_RESULTS.json','SOURCE_SELECTION.json']]
release,manifest,val,selection=[read(Path(x['path'])) for x in core]
assert core[1]['sha256']==release['publication_files_sha256']=='059d5d50594e1271ed57182275becc85484d7788a4313688ec23a6baede3df2f'
assert core[2]['sha256']==release['validation_results_sha256']=='c74594ede939ffb8422473f83c0b837ecc85dadf0e29cf027db6c1df8ae7bda1'
assert release['status']=='FINAL_RELEASE'
packet=[bound(R/x['path'],x) for x in manifest['files']]
top_pat=re.compile(r'(?m)^(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def|abbrev|namespace|end|open|section|noncomputable section)\b')
th_pat=re.compile(r'(?m)^(?P<private>private\s+)?(?:theorem|lemma)\s+(?P<name>[^\s({:]+)')
modules=[];sources=[]
for module,sel in selection.items():
 n=module.split('.')[-1]; folder=R/n
 pre=(folder/'baseline.lean').read_bytes();post=(folder/'candidate.lean').read_bytes()
 assert sha(pre)==sel['preimage_sha256'] and sha(post)==sel['postimage_sha256']==val['modules'][module]
 t0,t1=pre.decode(),post.decode();m0,m1=mask_comments_and_strings(t0),mask_comments_and_strings(t1)
 def parse(t,m):
  top=list(top_pat.finditer(m));headers=[];proofs={}
  for x in th_pat.finditer(m):
   a=proof_assignment(t,x.end(),len(t))+2
   end=next((y.start() for y in top if y.start()>a),len(t))
   h=t[x.start():a]
   headers.append(dict(name=x.group('name'),private=bool(x.group('private')),header=h,sha256=sha(h.encode())))
   proofs[x.group('name')]=(a,end,t[a:end])
  return headers,proofs
 h0,p0=parse(t0,m0);h1,p1=parse(t1,m1)
 assert h0==h1
 changed=[n for n in p0 if p0[n][2]!=p1[n][2]]
 expected={'P1HistoricalFourthFullCellLimit':['exists_tuplePlus_closed_uniform_threshold','tendsto_boxPlus_full_joint'],
           'P1OriginalCoarseFourthCellIntegral':['integrableOn_cellIntegrand','cellIntegral_eq_raw']}[n]
 assert changed==expected,(n,changed)
 # Strip only the four complete tactic bodies. This preserves every full
 # declaration header, definition, data expression, import and comment elsewhere.
 def stripped(t,p):
  for k in sorted(changed,key=lambda k:p[k][0],reverse=True):
   a,e,_=p[k];t=t[:a]+' <UNCHANGED-PROOF-BOUNDARY '+k+'> '+t[e:]
  return t
 assert stripped(t0,p0)==stripped(t1,p1)
 defs=[]
 top=list(top_pat.finditer(m0))
 for i,x in enumerate(top):
  if re.match(r'(?:noncomputable\s+)?(?:def|abbrev)\b',m0[x.start():]):
   e=top[i+1].start() if i+1<len(top) else len(t0)
   raw=t0[x.start():e];assert raw in t1
   defs.append(dict(raw=raw,sha256=sha(raw.encode())))
 for root in [B,Path('/workspace/goldbach-formalization')]:
  item=identity(root/'ImbalancedChen'/(n+'.lean'));assert item['sha256']==sha(post);sources.append(item)
 scope=read(folder/'static-provenance'/'MANUSCRIPT_API_SCOPE.json')
 before=(folder/'before-build.log').read_text();assert ('error:' in before and n in before)
 modules.append(dict(module=module,baseline_sha256=sha(pre),postimage_sha256=sha(post),
                     complete_headers=h0,raw_definitions=defs,changed_proofs=changed,
                     imports_definitions_numeric_constants_hypotheses_quantifiers_unchanged=True,
                     source_bytes_outside_changed_tactic_bodies_exact=True,
                     all_original_integrability_and_legal_domain_premises_preserved=True,
                     header_or_definition_syntax_exceptions=[],
                     substantive_mathematical_gap_or_new_assumption_found=False,
                     manuscript_scope=scope,
                     raw_failure=identity(folder/'before-build.log')))
outputs=[]
for module,parts in val['source_plus_five_outputs'].items():
 assert len(parts)==6
 outputs += [bound(B/p,e) for p,e in parts.items()]
commands=val['normal_commands']+val['kernel_commands']+[val['audit_command']]
assert len(commands)==5 and all(c['exit_code']==0 for c in commands)
for c in commands:
 assert sha((R/c['log']).read_bytes())==c['log_sha256']
 assert c['cwd']==str(B)
 assert c['argv'][:4]==['python3','/workspace/blue-build-tools/run_guarded.py','--state','/workspace/blue-build-tools/runtime-evidence/state.json']
runtime=read(R/'ACTUAL_RUNTIME_COMMANDS.json')
for path,event in runtime['actual_compiler_commands'].items():
 assert event['cwd']==str(B) and event['tool']=='lean'
 assert event['command'][:4]==[event['sysroot']+'/bin/lean-runtime','-t0','-j2','-M12288']
 assert path in event['input_args']
 assert '-DmaxRecDepth=100000' in event['input_args'] and '-DmaxHeartbeats=4000000' in event['input_args']
 if path==str(R/'PublicAudit.lean'):
  assert event['input_args']==val['audit_command']['argv'][7:]
 else:
  trace=read(B/('.lake/build/lib/lean/ImbalancedChen/'+Path(path).stem+'.trace'))
  lines=[x['message'] for x in trace['log'] if x['message'].startswith('.> LEAN_PATH=')]
  assert len(lines)==1
  tokens=shlex.split(lines[0][3:]);at=tokens.index(event['sysroot']+'/bin/lean')
  assert tokens[at+1:]==event['input_args']
exports=read(R/'PUBLIC_EXPORTS.json');log=(R/'types-axioms.log').read_text()
records=[json.loads(l.split('AUDIT_RECORD ',1)[1]) for l in log.splitlines() if 'AUDIT_RECORD ' in l]
assert len(records)==len(exports)==34
assert records==[{k:v for k,v in x.items() if k!='transitive_axioms'} for x in exports]
assert len({x['name'] for x in exports})==34
counts=dict(collections.Counter(x['module'] for x in exports))
assert counts==val['public_export_counts']==release['environment_public_export_counts']
assert counts=={'ImbalancedChen.P1HistoricalFourthFullCellLimit':13,'ImbalancedChen.P1OriginalCoarseFourthCellIntegral':21}
assert all(not x['is_axiom_declaration'] and '...' not in x['type_expression'] and 'sorryAx' not in x['type_expression'] for x in exports)
ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
noax=re.findall(r"'([^']+)' does not depend on any axioms",log)
assert len(ax)+len(noax)==34
am={n:{re.sub(r'\.\{[^}]*\}$','',s.strip()) for s in a.split(',')} for n,a in ax};am.update({n:set() for n in noax})
assert all(set(x['transitive_axioms'])==am[x['name']] for x in exports)
assert all(a<={'propext','Classical.choice','Quot.sound'} for a in am.values())
audit=(R/'PublicAudit.lean').read_text()
assert all(s in audit for s in ['env.constants.fold','env.getModuleIdxFor? name','!isPrivateName name','set_option pp.all true'])
assert 'AUDIT_FINISHED 34' in log
for item in core+packet+sources+outputs:assert identity(Path(item['path']))==item
report=dict(schema='independent_batch38_full_source_and_validation_review_v1',status='PASS_INDEPENDENT_REVIEW',
 reviewer='/root/retained_reuse',reviewed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 source_review=modules,final_release_inputs=core,original_manifest_file_count=len(packet),
 all_recorded_manifest_file_sha256_and_sizes_match=True,source_plus5_current_objects=outputs,
 source_main_Member_equal_recorded_postimages=sources,
 existing_validation=dict(actual_environment_public_counts=counts,total=34,normal_exit_codes=[0,0],kernel_exit_codes=[0,0],audit_exit_code=0,
                          full_AST_records_equal_raw_log=True,canonical_owner_enumeration=True,no_type_elisions=True,
                          transitive_axioms_equal_raw_log=True,only_standard_axioms=True,actual_guard_trace_argv_bound=True),
 findings=[],Lean_kernel_type_axiom_invocations_by_reviewer=0,live_or_original_packet_edits=0,
 limitations=['This verifies exactly two source postimages and their existing recorded Member import context, not complete P1 or complete blue-node closure.',
              'Historical fixed-mesh fourth and original coarse positive-cutoff integral objects remain distinct. No global small-prime/a→0/full-source premise is discharged by this review.',
              'The baseline source did not previously elaborate; no old kernel type-equality claim is made.'],
 late_addendum_handoff='Add this review and its separate file manifest to a new late addendum, without changing original FINAL_RELEASE/PUBLICATION_FILES/VALIDATION_RESULTS/raw logs.')
out=R/'INDEPENDENT_REVIEW.json';out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
addition=dict(schema='batch38_independent_review_late_addendum_v1',original_release=core[0],original_manifest=core[1],
              new_files=[identity(out),identity(Path(__file__))],original_packet_changed=False)
late=R/'INDEPENDENT_REVIEW_FILES.json';late.write_text(json.dumps(addition,indent=2)+'\n')
print(json.dumps(dict(review=identity(out),late=identity(late),headers=sum(len(m['complete_headers']) for m in modules),defs=sum(len(m['raw_definitions']) for m in modules)),indent=2))
