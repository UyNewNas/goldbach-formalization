from pathlib import Path
import collections, datetime, difflib, hashlib, json, os, re, subprocess

W=Path('/workspace');P=W/'p1-complete-proof';R=W/'goldbach-formalization'
O=P/'static-third-rounded-gap-stored-four'
D=P/'modern-p1-build/incremental-six-root-after-source-repairs'
F=D/'failure-observation-0007'
assert not O.exists(),'Do not overwrite a frozen packet.'
ENV=dict(os.environ,GIT_NO_LAZY_FETCH='1',GIT_TERMINAL_PROMPT='0')
def sha(b):return hashlib.sha256(b).hexdigest()
def rec(p,b=None):
 p=Path(p);b=p.read_bytes()if b is None else b
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def git(*args):return subprocess.run(['git','-C',str(R),*args],env=ENV,capture_output=True,check=True).stdout
def blob(c,p):
 h=git('rev-parse',c+':'+p).decode().strip();b=git('cat-file','blob',h)
 return b,{'commit':c,'path':p,'blob':h,'bytes':len(b),'sha256':sha(b)}
def mask(raw):
 out=bytearray(raw);i=0;depth=0
 while i<len(raw):
  if depth:
   if raw[i:i+2]==b'/-':depth+=1;out[i:i+2]=b'  ';i+=2
   elif raw[i:i+2]==b'-/':depth-=1;out[i:i+2]=b'  ';i+=2
   else:
    if raw[i]not in(10,13):out[i]=32
    i+=1
  elif raw[i:i+2]==b'/-':depth=1;out[i:i+2]=b'  ';i+=2
  elif raw[i:i+2]==b'--':
   j=raw.find(b'\n',i);j=len(raw)if j<0 else j
   for n in range(i,j):out[n]=32
   i=j
  else:i+=1
 assert depth==0
 return bytes(out)
RX=rb'(?m)^(?:@\[[^\n]*\][ \t]*)?(?:(private) )?(def|theorem|lemma|abbrev|structure) ([A-Za-z0-9_.\x80-\xff]+)\b'
def scan(raw):
 code=mask(raw);ms=list(re.finditer(RX,code));rows=[]
 for n,m in enumerate(ms):
  end=ms[n+1].start()if n+1<len(ms)else len(raw);dep=0;a=None
  for j in range(m.end(),end):
   b=code[j:j+1]
   if b in(b'(',b'{',b'['):dep+=1
   elif b in(b')',b'}',b']'):dep-=1;assert dep>=0
   if code[j:j+2]==b':='and dep==0:a=j;break
  assert a is not None
  rows.append({'name':m.group(3).decode(),'kind':m.group(2).decode(),'private':bool(m.group(1)),
   'start':m.start(),'assignment':a,'end':end,'header':raw[m.start():a+2]})
 return rows
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
negative_old=b'  have h := neg_le_neg (scaled_floor_div_le hd (-n))\n  simpa [up,value] using h\n'
negative_new=b'  have h := scaled_floor_div_le hd (-n)\n  simp only [up, value, Int.cast_neg, neg_div] at h \xe2\x8a\xa2\n  linarith only [h]\n'
configs=[
 {'short':'ActualThirdOriginalBelowMuBRounded','pre':'e74fffa458fe2f2ee71f26c10be65391f224119b2d5d5ccb713e0b4528f7780e',
  'post':'bf77f40ed681d3391d0f07493773196fd24637c46542d6e502991e8b643afbf0','commit':'f5415e467b95ae9b82ad8ae306e495b6d80a21e1',
  'path':'ImbalancedChen/ActualThirdOriginalBelowMuBRounded.lean','extra_eof_LF':1,
  'edits':[('le_scaled_up_div',negative_old,negative_new)],
  'scope':'Ordinary full B box below mu. Same P160, signed V division, old/new operand tree, full4*boxMass, log range1..32, original positivity/geometry/query premises; no new mean/chord/query or target bound premise.'},
 {'short':'ActualThirdOriginalRoundedOldWeight','pre':'e2fec9345e3b5d688c1be907aadd587e8f695f55217a8d37e79f89528a9520de',
  'post':'3bbaf4f839bb95a4e80d80e9406b04cadd112c85990700e8e61c38972e09f8d4','commit':'f5415e467b95ae9b82ad8ae306e495b6d80a21e1',
  'path':'ImbalancedChen/ActualThirdOriginalRoundedOldWeight.lean','extra_eof_LF':1,
  'edits':[('le_scaled_up_div',negative_old,negative_new),('rawWeight_encloses',
   b'  have h := divRat_sound (sub_sound (symmetricOld_encloses hlog hpositive hsquare)\n',
   '  have h := divRat_sound (sub_sound (symmetricOld_encloses (c := (c : ℝ)) (d := (d : ℝ)) hlog hpositive hsquare)\n'.encode())],
  'scope':'Same symmetric OLD max-moment expression, exact57/64 minorant and rational raw wt before clipping. Same c,d parameters become explicit only in an existing proof call. Positive log and squared-log divisor guards and endpoint query hypotheses stay unchanged.'},
 {'short':'P4AActualSquaredGapDecay','pre':'a45a0d9b1833d9ed687a24309759576487e4ccc5b646debfecd8632921fc1601',
  'post':'dcf58efadff04285ebc37e7e415c54e7a83c3709551ea4561bb9c81e5af02a88','commit':'f5415e467b95ae9b82ad8ae306e495b6d80a21e1',
  'path':'ImbalancedChen/P4AActualSquaredGapDecay.lean','extra_eof_LF':2,
  'edits':[('hasDerivAt_square_mul_normalized_gap',
   b'    simpa only [pow_two, id_eq, one_mul, mul_one] using\n      (hasDerivAt_id s).mul (hasDerivAt_id s)\n',
   b'    simpa only [pow_two, Pi.mul_apply, id_eq, one_mul, mul_one] using\n      (hasDerivAt_id s).fun_mul (hasDerivAt_id s)\n')],
  'scope':'Same actual normalized upper-lower gap on closedIci3, derivatives only s>3, no new D/F/f. Same square derivative2s, delayed-gap algebra and antitone propagation; arbitrary real anchor k>=3 and s>=k, exact quadratic tail unchanged.'},
 {'short':'ActualThirdOriginalStoredQueryAllBranches','pre':'839167b1e610ba542a19d5f4d6256cbd4ec0bcadb5e1b65b3c71c9517daab904',
  'post':'2a1b29dc2d1e3e22b8839f153ae07c52826898196fe6ec7f8de83c470ec6c4b5','commit':'51859a24c91580f885afd2a781dcb48b07177529',
  'path':'docs/source-only/20261112-resume/p2-repair-r2/repaired/ImbalancedChen/ActualThirdOriginalStoredQueryAllBranches.lean','extra_eof_LF':0,
  'edits':[('terminal_division_node_rounding',
   '  have hloQ := Int.floor_le ((lo : ℚ)/12)\n  have hhiQ := Int.le_ceil ((hi : ℚ)/12)\n'.encode(),
   '  have hloQ := Int.floor_le ((lo : ℚ)/((12 : ℤ) : ℚ))\n  have hhiQ := Int.le_ceil ((hi : ℚ)/((12 : ℤ) : ℚ))\n'.encode())],
  'scope':'Same signed lo/hi outward division by12, P112 nodes and P160 rescaling, lower terminalLlo and upper terminalHhi, zero clamp including negative numerator, all40 checked-block reader explicit, total all3branches for arbitrary integer a and positive b. No desired query, range gate, saved output, table instance or new analytic premise.'},
]
ledger_raw=(F/'ACTUAL_FAILURES.json').read_bytes();assert sha(ledger_raw)=='ec0cff1483b56d8d26917fa07ffaedff69decaa4f129c98212c1dd64b9da1a8f'
ledger=json.loads(ledger_raw);assert not ledger['whole_normal_controller_still_running']and ledger['actual_normal_exit_code']==1
log=(F/'actual-completed-normal.log').read_bytes();assert(len(log),sha(log))==(ledger['actual_log_bytes'],ledger['actual_log_sha256'])
command_raw=(D/'COMMAND.json').read_bytes();command=json.loads(command_raw);assert command['exit_code']==1 and command['log_sha256']==sha(log)
assert command['finished_utc']==ledger['actual_normal_finished_utc']
context_raw=(D/'SOURCE_CONTEXT.json').read_bytes();assert sha(context_raw)==command['source_context_sha256']=='db2dfc6e2ae8357ded33da4d3f5f938284db78ebaf5d6caa17d097d4ff5f3538'
context=json.loads(context_raw)
O.mkdir();files=[]
def put(name,b):
 p=O/name;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb')as f:f.write(b)
 v={'path':p.relative_to(O).as_posix(),'bytes':len(b),'sha256':sha(b)};files.append(v);return v
def putj(name,v):return put(name,(json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
put('prepare_third_rounded_gap_stored_four.py',Path(__file__).read_bytes())
put('provenance/ACTUAL_FAILURES_0007.json',ledger_raw);put('provenance/ACTUAL_COMPLETED_COMMAND.json',command_raw)
put('provenance/actual-completed-normal.log',log);put('provenance/SOURCE_CONTEXT.json',context_raw)
put('provenance/KNOWN_NARROW_PUBLISHED_VARIANTS.json',Path('/tmp/third-rounded-gap-stored-published-narrow.json').read_bytes())
modules={};inventory={};allheads=0;alldefs=0;allthms=0
for cfg in configs:
 n=cfg['short'];module='ImbalancedChen.'+n;source=W/'blue-member-build/ImbalancedChen'/(n+'.lean')
 before=source.read_bytes();assert sha(before)==cfg['pre']
 binding=context['effective_source_bindings'][module];assert(binding['sha256'],binding['bytes'])==(sha(before),len(before))
 after,upstream=blob(cfg['commit'],cfg['path']);assert sha(after)==cfg['post']
 base_payload,base_origin=blob('b2c20e789cd9026661bbc11eaae0e53fba9e94e5','ImbalancedChen/'+n+'.lean');assert base_payload==before
 forward=before
 for proof,old,new in cfg['edits']:
  assert forward.count(old)==1;forward=forward.replace(old,new,1)
 forward+=b'\n'*cfg['extra_eof_LF'];assert forward==after
 reverse=after[:-cfg['extra_eof_LF']]if cfg['extra_eof_LF']else after
 for proof,old,new in reversed(cfg['edits']):assert reverse.count(new)==1;reverse=reverse.replace(new,old,1)
 assert reverse==before
 comparable=after[:-cfg['extra_eof_LF']]if cfg['extra_eof_LF']else after
 oldscan=scan(before);newscan=scan(comparable);assert len(oldscan)==len(newscan)
 headers=[];defs=[];changed=[]
 for x,y in zip(oldscan,newscan,strict=True):
  assert(x['name'],x['kind'],x['private'],x['header'])==(y['name'],y['kind'],y['private'],y['header'])
  headers.append({'name':x['name'],'kind':x['kind'],'private':x['private'],'complete_before_raw_header':x['header'].decode(),'complete_after_raw_header':y['header'].decode(),'sha256':sha(x['header']),'exact':True})
  a=before[x['assignment']+2:x['end']];b=comparable[y['assignment']+2:y['end']]
  if x['kind']in('def','abbrev','structure'):
   assert a==b
   region=before[x['start']:x['end']]
   defs.append({'name':x['name'],'complete_raw_region':region.decode(),'bytes':len(region),'sha256':sha(region),'before_after_exact':True})
  elif a!=b:changed.append(x['name'])
 assert changed==list(dict.fromkeys(p for p,_,_ in cfg['edits']))
 assert re.findall(rb'(?m)^import[^\r\n]*',before)==re.findall(rb'(?m)^import[^\r\n]*',after)
 assert re.findall(rb'(?m)^set_option[^\r\n]*',before)==re.findall(rb'(?m)^set_option[^\r\n]*',after)==[]
 assert re.findall(rb'\b(?:sorry|admit|native_decide|run_tac)\b',mask(after))==[]
 assert b'\r'not in before+after
 entry,=[x for x in ledger['modules']if x['module']==module];assert entry['actual_lean_exit_code']==1
 assert entry['source_sha256_at_initial_failure']==entry['current_sha256_at_observation']==sha(before)
 slice_raw=(F/entry['raw_failure_slice']).read_bytes();assert sha(slice_raw)==entry['slice_sha256']
 assert log[entry['raw_byte_start']:entry['raw_byte_end_exclusive']]==slice_raw
 assert b'error: Lean exited with code 1'in slice_raw
 sub=n+'/'
 pre=put(sub+'baseline.lean',before);post=put(sub+'candidate.lean',after)
 put(sub+'candidate.patch',''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile='actual-failed-pre/'+n+'.lean',tofile=cfg['commit'][:12]+'/'+n+'.lean')).encode())
 failure=put(sub+'ACTUAL_FAILURE_SLICE.log',slice_raw)
 public_count=sum(not x['private']for x in oldscan);private_count=sum(x['private']for x in oldscan)
 counts={'full_source_commands':len(oldscan),'public_source_commands':public_count,'private_source_commands':private_count,'theorems_including_private':sum(x['kind']in('theorem','lemma')for x in oldscan),'definitions':len(defs)}
 item={'module':module,'author':'EXACT_PUBLISHED_SOURCE_REUSE_NO_NEW_PROOF','status':'ISOLATED_UNCOMPILED_PENDING_NONAUTHOR_GATE_AND_OWNER_ACTUAL_VALIDATION',
  'baseline':pre,'candidate':post,'live_selected_preimage':rec(source,before),'initial_context_binding':binding,'baseline_published_origin':base_origin,
  'exact_whole_post_publication':upstream,'all_published_post_bytes_including_original_comments_and_EOF_retained':True,
  'header_definition_semantic_or_syntax_exceptions':[],'counts':counts,'proof_bodies_changed_relative_to_failed_pre':changed,
  'only_nonproof_byte_difference':{'classification':'PUBLISHED_TRAILING_EOF_WHITESPACE_ONLY','additional_LF_bytes':cfg['extra_eof_LF'],'removed_or_normalized':False},
  'all_complete_headers_definitions_imports_options_comments_namespaces_data_hypotheses_and_quantifiers_preserved':True,
  'full_original_source_reverse_byte_exact':True,'mathematical_scope':cfg['scope'],
  'actual_failure':{'owner_ledger_entry':entry,'slice':failure,'whole_completed_log':rec(F/'actual-completed-normal.log',log),'complete_aggregate_exit_code':1,'individual_unit_exit_code':1,'job_label_is_wall_label_not_CPU_time':True},
  'candidate_normal_kernel_audit_success_not_claimed':True,'new_hypotheses_axioms_numeric_algorithm_or_budget_increase':False}
 modules[module]=item
 inv={'module':module,'counts':counts,'all_complete_headers':headers,'all_complete_definition_regions':defs,'proof_delta_fragments':[{'proof':p,'before':a.decode(),'after':b.decode(),'before_sha256':sha(a),'after_sha256':sha(b)}for p,a,b in cfg['edits']],
  'added_published_trailing_EOF_LF_bytes':cfg['extra_eof_LF'],'only_allowed_proof_fragments_plus_exact_published_EOF_reconstruct_candidate':True,'whole_original_reverse_sha256':sha(reverse),'no_header_or_def_exceptions':True}
 putj(sub+'COMPLETE_HEADERS_DEFINITIONS_AND_EXACT_REVERSE.json',inv)
 inventory[module]=counts;allheads+=len(headers);alldefs+=len(defs);allthms+=counts['theorems_including_private']

api=[]
def excerpt(relative,lo,hi,role,root=W/'blue-member-build'):
 path=root/relative;raw=path.read_bytes();part=b''.join(raw.splitlines(True)[lo-1:hi]);api.append({'source':rec(path,raw),'start_line':lo,'end_line':hi,'role':role,'raw_excerpt':part.decode(),'excerpt_sha256':sha(part)})
excerpt('ImbalancedChen/ActualThirdOriginalRoundedNewOperations.lean',10,21,'Original IV lo/hi, Encloses and up(n,d)=-((-n)/d); no sign restriction on n.')
excerpt('ImbalancedChen/ActualThirdOriginalFixedpointClippedChord.lean',11,16,'Original P160=2^160 and value(z)=z/P160.')
excerpt('ImbalancedChen/ActualThirdOriginalRationalQuery.lean',20,30,'Original rational floor/ceil by explicitly cast integer denominator, valid for all signed x and d>0.')
excerpt('.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean',258,270,'@[to_fun] on HasDerivAt.mul generates HasDerivAt.fun_mul with same derivative and explicit pointwise product.',R)
excerpt('.lake/packages/mathlib/Mathlib/Tactic/ToFun.lean',13,39,'Actual attribute naming and eta-expansion contract for generated fun_mul.',R)
excerpt('.lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean',64,72,'Pi.mul_apply exposes pointwise multiplication without any new mathematical assumption.',R)
excerpt('.lake/packages/mathlib/Mathlib/Algebra/Order/Floor/Ring.lean',283,294,'Current Int.floor_div_cast_of_nonneg signature retains positive divisor via hd.le, including signed numerator.',R)
excerpt('.lake/packages/mathlib/Mathlib/Algebra/Order/Floor/Defs.lean',297,326,'Int.floor_le and Int.le_ceil do not require a nonnegative real/rational numerator.',R)
putj('PINNED_API.json',{'schema':'four_existing_published_proofs_current_API_binding_v1','sources':api,'no_elaboration_of_candidates_or_generated_API_declarations_performed':True})
paper=W/'chen-imbalanced-semiprimes/paper/release-20261106/en/numerical-appendix.tex';raw=paper.read_bytes()
paperrec=rec(paper,raw);anchors=[]
for lo,hi,role in [(95,104,'Directed floor/ceil interval rounding; positive denominator check only.'),(122,143,'Original actual upper/lower numerator recurrence and whole-support queries.'),(202,212,'D=(F-f)/(2exp gamma), delay equation, monotonicity and quadratic tail.' )]:
 part=b''.join(raw.splitlines(True)[lo-1:hi]);r=put(f'provenance/numerical-appendix-{lo}-{hi}.tex',part);anchors.append({'original_source':paperrec,'range':[lo,hi],'snapshot':r,'meaning':role})
putj('MANUSCRIPT_SCOPE.json',{'commit':'a988cba584d803ae2856a0de50efb582f4f3dd6a','release':'paper/release-20261106/en','anchors':anchors,
 'boundary':'Existing Nov6 interval and actual-gap statements only. No new analytic theorem, modified physical policy, row data, target-gain oracle, saved output or discarded sign/cutoff is supplied. Existing conditional query/checked-reader premises remain explicit.'})
for name,path in [('P2_R2_SOURCE_ONLY_HISTORY.txt',R/'docs/source-only/20261112-resume/p2-repair-r2/REPAIR_REPORT.txt')]:put('provenance/'+name,path.read_bytes())
putj('SOURCE_SELECTION.json',{'schema':'four_actual_third_rounding_gap_query_exact_published_source_candidates_v1','prepared_utc':now,'preparer':'/root/omega_review',
 'status':'SOURCE_ONLY_UNCOMPILED_EXACT_PUBLISHED_POST_REUSE','modules':modules,'module_count':4,'total_complete_source_headers':allheads,'total_definition_regions':alldefs,'total_theorems_including_private':allthms,
 'actual_completed_aggregate_command':rec(D/'COMMAND.json',command_raw),'actual_completed_aggregate_log':rec(F/'actual-completed-normal.log',log),'owner_failure_0007':rec(F/'ACTUAL_FAILURES.json',ledger_raw),
 'bounded_reuse_search':'Only the four known source inventory entries and seven exact-path all-ref commits returned by their filename log; known r2/r3 source-only post paths. No repository-wide history, native/import qualification or remote fetch.',
 'old_SOURCE_ONLY_comments_kept_as_exact_published_history':True,'no_Lean_Lake_LSP_normal_kernel_type_axiom_numeric_or_stock_calls':True,
 'no_live_main_Member_P6_cache_runtime_guard_queue_controller_or_old_record_mutations':True,'next_step':'Independent exact-source review; then soleowner safe adoption and original-guard normal/kernel/full-owned/source+five checks. Published source presence or prior static source history is not current acceptance.','whole_P1_complete':False})
putj('COUNTS_AND_BOUNDARIES.json',{'modules':inventory,'totals':{'full_source_headers':allheads,'definition_regions':alldefs,'theorems_including_private':allthms},
 'exact_whole_post_sources_reused':4,'new_Lean_proof_code_written':0,'public_header_or_definition_exceptions':[],
 'only_nonproof_byte_deltas':'Raw published trailing EOF whitespace: BelowMuB+1LF, OldWeight+1LF, SquaredGap+2LF, StoredQuery+0. All original EOLs are LF and remain LF; no comments/import/options/data/header modifications.',
 'raw_decl_counts_are_not_environment_owned_acceptance_counts':True})
put('README.md',('Four actual0007 failures, all repaired by exact existing published bytes.\n\n'
 'BelowMuB, OldWeight and SquaredGap are raw f5415e467b95ae9b82ad8ae306e495b6d80a21e1 canonical source blobs; StoredQuery is raw51859a24c91580f885afd2a781dcb48b07177529 p2-repair-r2/repaired source blob. No proof code was invented. Each module binds baseline/current initial context, exact pre/post Git objects, real completed failure slice, full raw headers/defs and complete forward/reverse reconstruction.\n\n'
 'The first three public files retain their original published extra EOF blank lines (1/1/2 LF); this is explicitly the only nonproof-byte delta. No old comment is edited. All imports, headers, definitions, data, hypotheses, constants, precision and resource options remain. Source-only historical reports do not claim current normal/kernel/audit acceptance.\n\n'
 'Negative numerators remain allowed; ceiling follows the original lower floor bound at -n. OldWeight only makes its existing c,d proof parameters explicit. SquaredGap uses the published eta-expanded fun_mul API, preserving the actual factors and arbitrary real anchors. StoredQuery retains negative zero-clamp, same P112/P160 normalization, all3 branches and the all40 explicit checked reader, with terminal Llo/Hhi unchanged.\n\n'
 'UNCOMPILED candidates only. No live source/cache/runtime/guard/queue/controller modifications or Lean/Lake/stock/kernel/audit/numeric calls. Soleowner alone adopts at a safe target window and performs actual validation.\n').encode())
putj('FILES_MANIFEST.json',{'schema':'relative_four_exact_published_source_candidate_files_v1','files':sorted(files,key=lambda x:x['path']),'manifest_excludes_itself':True,'old_records_unchanged':True})
for n in ['SOURCE_SELECTION.json','FILES_MANIFEST.json','COUNTS_AND_BOUNDARIES.json']:print(json.dumps(rec(O/n)))
print(json.dumps({'counts':inventory,'total_headers':allheads,'defs':alldefs,'theorems':allthms}))
