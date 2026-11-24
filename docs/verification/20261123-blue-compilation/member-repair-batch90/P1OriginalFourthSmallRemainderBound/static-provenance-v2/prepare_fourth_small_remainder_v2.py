from pathlib import Path
import ast,datetime,difflib,hashlib,json,re
W=Path('/workspace');P=W/'p1-complete-proof';O=P/'static-fourth-small-remainder-v2'
assert not O.exists()
def sha(b):return hashlib.sha256(b).hexdigest()
def rec(p,b=None):
 p=Path(p);b=p.read_bytes()if b is None else b
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
source=W/'blue-member-build/ImbalancedChen/P1OriginalFourthSmallRemainderBound.lean'
before=source.read_bytes();assert sha(before)=='b2b6faf5300f3a59ae73271d2f66a9315f8d3fbf59eee1a869a2298023c65ac1'
old=b'          add_le_add_left hfirst _\n';new=b'          add_le_add le_rfl hfirst\n'
assert before.count(old)==1;after=before.replace(old,new,1);assert after.replace(new,old,1)==before
assert b'          add_le_add le_rfl hsecond\n'in before
parser=ast.parse(Path('/tmp/prepare_third_rounded_gap_stored_four.py').read_text())
nodes=[n for n in parser.body if isinstance(n,ast.FunctionDef)and n.name in('mask','scan')or isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='RX'for t in n.targets)]
ns={'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),'existing-comment-aware-parser','exec'),ns)
a=ns['scan'](before);b=ns['scan'](after);headers=[];defs=[];changed=[]
for x,y in zip(a,b,strict=True):
 assert(x['name'],x['kind'],x['private'],x['header'])==(y['name'],y['kind'],y['private'],y['header'])
 headers.append({'name':x['name'],'kind':x['kind'],'private':x['private'],'complete_before_raw_header':x['header'].decode(),'complete_after_raw_header':y['header'].decode(),'sha256':sha(x['header'])})
 left=before[x['assignment']+2:x['end']];right=after[y['assignment']+2:y['end']]
 if x['kind']in('def','abbrev','structure'):
  assert left==right;raw=before[x['start']:x['end']];defs.append({'name':x['name'],'complete_raw_region':raw.decode(),'bytes':len(raw),'sha256':sha(raw)})
 elif left!=right:changed.append(x['name'])
assert len(changed)==1
D=W/'blue-member-repair-batch90';log=(D/'P1OriginalFourthSmallRemainderBound-normal.log').read_bytes()
assert(len(log),sha(log))==(171123,'130277c80e9f17d5d4525c4b95da27885e49beb6ef39bb5e826c6ba976144f5c')
cmdraw=(D/'P1OriginalFourthSmallRemainderBound-normal-command.json').read_bytes();cmd=json.loads(cmdraw)
assert cmd['exit_code']==1 and cmd['log_sha256']==sha(log)
assert cmd['argv'][3].endswith('/runtime-evidence/state.json')
heads=re.findall(rb'(?m)^error: ImbalancedChen/P1OriginalFourthSmallRemainderBound\.lean:(\d+):',log);assert heads==[b'254']
assert b'add_le_add_left hfirst'in log
v1=P/'static-fourth-prefix-splice-pairroot';prior=(v1/'INDEPENDENT_ROOT_STATIC_REVIEW.json').read_bytes();assert sha(prior)=='a57e7bd9b8b1d0ebfdd9d8baac13d340574c917d52da9c8929b35969f84d9f79'
assert(v1/'P1OriginalFourthSmallRemainderBound/candidate.lean').read_bytes()==before
oldapi=json.loads((v1/'PINNED_API_MANUSCRIPT_AND_REUSE.json').read_bytes())
api=next(x for x in oldapi['pinned_API']if x['path'].endswith('/Algebra/Order/Monoid/Defs.lean'))
apiraw=Path(api['path']).read_bytes();assert sha(apiraw)==api['sha256']
assert b''.join(apiraw.splitlines(True)[api['start_line']-1:api['end_line']]).decode()==api['raw_excerpt']
O.mkdir();files=[]
def put(n,b):
 q=O/n;q.parent.mkdir(parents=True,exist_ok=True)
 with q.open('xb')as f:f.write(b)
 r={'path':q.relative_to(O).as_posix(),'bytes':len(b),'sha256':sha(b)};files.append(r);return r
def putj(n,v):return put(n,(json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
pre=put('baseline.lean',before);post=put('candidate.lean',after)
put('candidate.patch',''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile='actual-b2b6-pre',tofile='same-left-addition-API-v2')).encode())
put('ACTUAL_NORMAL_FAILURE.log',log);put('ACTUAL_NORMAL_COMMAND.json',cmdraw)
put('prior-evidence/V1_INDEPENDENT_ROOT_STATIC_REVIEW.json',prior)
put('prepare_fourth_small_remainder_v2.py',Path(__file__).read_bytes())
putj('COMPLETE_HEADERS_DEFINITIONS_AND_EXACT_DELTA.json',{'schema':'single_same_left_addition_proof_call_complete_source_delta_v1','complete_headers':headers,'complete_definition_regions':defs,'changed_theorem':changed[0],'before_fragment':old.decode(),'after_fragment':new.decode(),'only_one_fragment':True,'whole_reverse_exact':True,'reverse_sha256':sha(before),'all_other_source_bytes_preserved':True,'header_definition_or_semantic_exceptions':[]})
putj('PINNED_API_AND_REUSE.json',{'current_API':api,'same_proof_existing_after_line': 'add_le_add le_rfl hsecond','existing_accepted_addition_recipe':oldapi['accepted_reuse']['same_left_addition'],'manuscript_context_reused_from_original_non_author_review':oldapi['manuscript_context'],'mechanism':'The actual goal is A+B<=A+C. add_le_add_left hfirst has B+?<=C+? at this pin. add_le_add le_rfl hfirst produces the exact same-left goal and is already the recipe used immediately afterward for hsecond. No inequality, sign, budget or variable changes.'})
putj('SOURCE_SELECTION.json',{'schema':'actual_remainder90_v2_one_proof_API_call_candidate_v1','preparer':'/root/omega_review','prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'ISOLATED_UNCOMPILED_PENDING_NONAUTHOR_GATE_AND_OWNER_VALIDATION','module':'ImbalancedChen.P1OriginalFourthSmallRemainderBound','baseline':pre,'candidate':post,'v1_source_sha256':sha(before),'v1_root_review_sha256':sha(prior),'all_previous_v1_edits_retained':True,'actual_v1_normal_failure':{'command':rec(D/'P1OriginalFourthSmallRemainderBound-normal-command.json',cmdraw),'raw_log':rec(D/'P1OriginalFourthSmallRemainderBound-normal.log',log),'exit_code':1,'elapsed_seconds':cmd['elapsed_seconds'],'only_actual_error_location':'254:10'},'counts':{'full_headers':len(headers),'complete_defs':len(defs)},'only_changed_theorem':changed[0],'only_changed_fragment':{'before':old.decode(),'after':new.decode()},'all_headers_defs_data_constants_hypotheses_quantifiers_targets_imports_comments_EOL_and_options_raw_exact':True,'header_or_definition_exceptions':[],'entire_source_exact_reverse':True,'new_Lean_Lake_normal_kernel_type_axiom_numeric_or_stock_calls':0,'live_main_Member_P6_cache_guard_runtime_queue_controller_or_old_record_mutations':False,'earlier_successful_PrefixWinner_Splice_or_other_modules_not_rebuilt':True,'candidate_success_not_claimed':True})
putj('FILES_MANIFEST.json',{'schema':'relative_remainder90_one_call_v2_candidate_files_v1','files':files.copy(),'manifest_excludes_itself':True,'old_records_unchanged':True})
for n in ['candidate.lean','SOURCE_SELECTION.json','FILES_MANIFEST.json']:print(json.dumps(rec(O/n)))
print('headers',len(headers),'defs',len(defs),'changed',changed)
