#!/usr/bin/env python3
"""Reproduce the frozen original P1.4 legacy-evidence review without compilation.

Read repository evidence only. The required output path must be new; neither
existing evidence nor a previous output is overwritten. No runtime object
identity or whole-P1.4 completion is inferred from this metadata review.
"""
from pathlib import Path
import argparse
import hashlib,json,re
if not __debug__:
 raise RuntimeError('P1.4 evidence verification requires assertions; optimized execution is forbidden')
REPO=Path(__file__).resolve().parents[4]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',required=True,type=Path,
                    help='New JSON output path; its parent directory must exist.')
ARGS=parser.parse_args()
BASE=REPO/'docs/verification/20261123-blue-compilation'
def sha(b):return hashlib.sha256(b).hexdigest()
def file(p):
 b=p.read_bytes();return {'path':str(p.relative_to(REPO)), 'bytes':len(b),'sha256':sha(b)}
def load(p):return json.loads(p.read_bytes())
ANSI=re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]');BUILT=re.compile(r'^\s*[✔⚠ℹ]\ufe0f?\s+\[[^\]\r\n]+\]\s+Built\s+(ImbalancedChen(?:\.[A-Za-z0-9_]+)+)(?::olean)?(?=\s|$)',re.M)
report={'schema':'p14_legacy_original_evidence_read_only_review_v1','baseline_commit':'28faf9d2b028997dfe7669b6750c0be5649c9ee4','remote_runtime_objects_checked':False,'source_or_frozen_files_changed':False,'compiler_kernel_audit_invoked':False,'whole_P1_4_complete':False,'owners':{},'reference_apis':[]}
for batch,short,owned in [('member-repair-batch3','P5OriginalSignedMidpoint',False),('member-repair-batch96','P5OriginalTaylorFiveDimensionalMidpoint',True),('member-repair-batch84','P5SubdivisionStoredParentArchive',True)]:
 p=BASE/batch;m='ImbalancedChen.'+short;r=load(p/'VALIDATION_RESULTS.json');s=REPO/(m.replace('.','/')+'.lean');assert sha(s.read_bytes())==r['modules'][m]
 snap=r['source_plus_five_outputs'][m];assert len(snap)==6 and snap[m.replace('.','/')+'.lean']=={'bytes':s.stat().st_size,'sha256':sha(s.read_bytes())}
 assert load(p/(short+'-AFTER_NORMAL.json'))==snap and load(p/(short+'-AFTER_KERNEL.json'))==snap
 evidence=[file(s),file(p/'VALIDATION_RESULTS.json'),file(p/(short+'-AFTER_NORMAL.json')),file(p/(short+'-AFTER_KERNEL.json'))]
 for kind in ['normal','kernel']:
  cmd=next(x for x in r[kind+'_commands'] if x['name']==short+'-'+kind)
  assert cmd['exit_code']==0 and cmd['cwd']=='/workspace/blue-member-build'
  cp=p/(short+'-'+kind+'-command.json');assert load(cp)==cmd
  lp=p/cmd['log'];assert sha(lp.read_bytes())==cmd['log_sha256'];evidence.extend([file(cp),file(lp)])
  if kind=='normal':assert BUILT.findall(ANSI.sub('',lp.read_text()))==[m]
  else:assert lp.read_text().strip()=='replaying '+m
 assert r['only_standard_axioms'] and r['pp_all_true_no_elisions'] and r['source_plus_five_outputs_unchanged_across_kernel_and_audit']
 command=r['audit_command'];lp=p/command['log'];assert command['exit_code']==0 and sha(lp.read_bytes())==command['log_sha256'];text=lp.read_text();assert not any(x in text for x in ['sorryAx','…','⋯','...'])
 evidence.extend([file(lp),file(p/'PUBLIC_EXPORTS.json'),file(p/'INDEPENDENT_REVIEW.json')])
 records=[json.loads(x) for x in re.findall(r'AUDIT_RECORD (\{[^\n]+\})',text)]
 if owned:
  assert r['status']=='PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS' and r['full_owned_including_private_generated']
  inventories=[json.loads(x)['names'] for x in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})',text)]
  assert len(inventories)==1 and sorted(inventories[0])==sorted(x['name'] for x in records) and len(set(inventories[0]))==len(records)
  assert all(x['kind']!='axiom' and set(x['axioms']) <= {'propext','Classical.choice','Quot.sound'} for x in records)
  assert all(isinstance(x['type'],str) and isinstance(x['type_expression'],str) and isinstance(x['universe_parameters'],list) and not any(t in x['type'] or t in x['type_expression'] for t in ['sorryAx','…','⋯','...']) for x in records)
  selected=[x for x in records if x['module']==m];stored=[x for x in load(p/'OWNED_EXPORTS.json') if x['module']==m];assert selected==[{k:v for k,v in x.items() if k not in ['transitive_axioms','is_axiom_declaration']} for x in stored]
  assert all(x['transitive_axioms']==x['axioms'] and x['is_axiom_declaration']==(x['kind']=='axiom') for x in stored)
  assert len(selected)==r['owned_export_counts'][m] and sum(not x['is_private'] for x in selected)==r['public_export_counts'][m]
  assert [x for x in stored if not x['is_private']]==[x for x in load(p/'PUBLIC_EXPORTS.json') if x['module']==m]
  evidence.append(file(p/'OWNED_EXPORTS.json'));template=p/('PublicAudit.lean' if batch.endswith('96') else 'ArchiveOnlyAudit.lean');evidence.append(file(template))
  result={'classification':'EXISTING_COMPLETE_NORMAL_KERNEL_FULL_OWNED_EVIDENCE_SAME_CURRENT_SOURCE','owned':len(selected),'public':sum(not x['is_private'] for x in selected),'private':sum(x['is_private'] for x in selected),'declaration_names':[x['name'] for x in selected],'whole_raw_log_inventory_verified':True,'decoded_type_and_AST_no_elisions':True,'live_six_artifacts_need_readonly_identity_check_before_runtime_reuse':True}
 else:
  assert r['status']=='PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_PUBLIC_TYPES_AXIOMS'
  selected=[x for x in load(p/'PUBLIC_EXPORTS.json') if x['module']==m];assert len(selected)==7
  assert all(set(x['transitive_axioms']) <= {'propext','Classical.choice','Quot.sound'} and not x['is_axiom_declaration'] for x in selected)
  log_selected=[x for x in records if x['module']==m]
  assert [{k:v for k,v in x.items() if k!='transitive_axioms'} for x in selected]==log_selected
  template=p/'PublicAudit.lean';assert 'targets.contains owner && !isPrivateName name' in template.read_text();evidence.append(file(template))
  result={'classification':'EXISTING_NORMAL_KERNEL_PUBLIC_AUDIT_SAME_CURRENT_SOURCE_COMPLETE_OWNED_STILL_MISSING','public':7,'full_owned_count_not_assumed':True,'private_source_theorems':['anchored_remainder','half_weight_integral'],'declaration_names':[x['name'] for x in selected],'no_repeated_normal_or_kernel_needed_if_live_six_artifacts_match':True}
 report['owners'][m]={**result,'source_sha256':sha(s.read_bytes()),'source_plus_five_original_snapshot':snap,'evidence_files':evidence}
for rel in ['docs/p1/20261125/p14-continuation/run_stage.py','docs/p1/20261125/batch13-repairs/run_repairs.py','docs/p1/20261124/normal-supplement-audit/run_parallel_acceptance_multibatch.py','docs/verification/20261123-blue-compilation/member-repair-batch84/seed42-owned-only/run_owned_only.py','docs/verification/20261123-blue-compilation/member-repair-batch84/seed42-owned-only/OwnedOnlyAudit.lean','docs/verification/20261123-blue-compilation/member-repair-batch84/seed42-owned-only/SEED42_COMPLETE_OWNED_SUPPLEMENT_RESULT.json']:
 report['reference_apis'].append(file(REPO/rel))
commandp=BASE/'member-repair-batch96/P5OriginalTaylorFiveDimensionalMidpoint/static-provenance/ACTUAL_COMMAND.json';cmd=load(commandp);m='ImbalancedChen.P5RecordedOldFifthBlockTotals';assert m in cmd['actual_Built_project_modules'];report['owners'][m]={'classification':'ORIGINAL_NORMAL_PRECISE_LOCATOR_FOUND_RAW_LOG_AND_SOURCE_CONTEXT_NOT_READ_HERE','current_source_sha256':sha((REPO/(m.replace('.','/')+'.lean')).read_bytes()),'locator_file':file(commandp),'original_normal_log':{'path':'/workspace/p1-complete-proof/modern-p1-build/incremental-six-root-after-source-repairs/normal.log','sha256':cmd['log_sha256']},'original_source_context':{'path':cmd['source_context'],'sha256':cmd['source_context_sha256']},'original_whole_batch_exit_code':cmd['exit_code'],'command_reports_actual_Built_module':True,'normal_or_complete_acceptance_granted':False}
report['integration_recommendation']={'immutable_run_stage_or_batch13_normal_one':'Do not call for these old ready objects: it requires its own NORMAL_PASS layout and will reject READY_WITHOUT_NORMAL_PROVENANCE. Never synthesize that record with a current dependency_context.','e9_multibatch_runner':'Can reuse old SHA-bound normal logs but always invokes named leanchecker; therefore it repeats already reliable Signed/Taylor/Archive kernel checks. It is potentially suitable for Recorded if original normal source context and absence of matching complete kernel audit are verified.','signed_full_owned_only':'Use the existing seed42-owned-only pattern with reviewed target/path/receipt pins and existing immutable full-owned template. Read and compare all six live files against the authentic batch3 original snapshot before and after; hash-check original normal/kernel command+logs+snapshot and exit0. Hold existing serializer/guard; invoke only a fresh audit module; audit dynamic environment owner inventory including all private/generated names, full type AST/universes/standard axioms. Preserve original receipts and identify the new receipt as a supplement, never NORMAL_PASS.','taylor_archive':'No Lean/kernel/full-owned repetition: complete historical same-source evidence is present. Read-only live six-file equality check is still required before claiming the current remote artifacts match these exact accepted originals.','counting':'Only Taylor18 and Archive13 are complete historical owner evidence in this review. Do not add these to existing cumulative totals until deduplication with prior accepted owner sets is confirmed.'}
raw=(json.dumps(report,ensure_ascii=False,indent=2)+'\n').encode()
assert sha(raw)=='8d85bd418d3d4df79c584b78d0ab793999fbec77c3cc3ec8568f0545ae776058', 'legacy evidence no longer reproduces the frozen review'
frozen=Path(__file__).resolve().with_name('REUSED_LEGACY_MIDPOINT_ARCHIVE.json')
assert frozen.read_bytes()==raw, 'frozen legacy review differs'
p=ARGS.output
with p.open('xb') as output:
 output.write(raw)
print(json.dumps({'path':str(p),'bytes':len(raw),'sha256':sha(raw),'owners':{k:{q:v[q] for q in ['classification','owned','public','private'] if q in v} for k,v in report['owners'].items()}},ensure_ascii=False,indent=2))
