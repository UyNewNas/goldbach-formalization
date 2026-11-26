from pathlib import Path
import json,hashlib,re
base=Path('/tmp/p24-recursion-repairs-20261126')
out=base/'concrete-run'
final=out/'attempt-006'
receipt=json.loads((final/'receipt.json').read_bytes())
status=json.loads((final/'status.json').read_bytes())
assert status['exit_code']==0 and not status['log_truncated'] and status['log_discarded_bytes']==0
assert receipt['all_three_stages_passed'] and receipt['wrapper_exit_code']==0
assert [s['stage'] for s in receipt['stages']]==['compile','replay','audit']
assert all(s['exit_code']==0 and not s['timed_out'] for s in receipt['stages'])
assert all(receipt['postchecks'].values()) and not receipt['postcheck_errors']
assert receipt['audit_summary']['all_safe_nonpartial_nonaxiom'] and receipt['audit_summary']['exact_inventory']
assert receipt['audit_summary']['allowed_axioms_only']
template=Path('/workspace/scratch/558c6ad37524/p24-recovery/diagnostics/datacore-import-command-01/OriginalAuditTemplate.lean').read_bytes()
assert hashlib.sha256(template).hexdigest()=='2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b'
assert template.count(b'ImbalancedChen.P2Winner9FiniteMomentKernel')==2
audit=template.replace(b'ImbalancedChen.P2Winner9FiniteMomentKernel',b'ConcreteRunCandidate')
info=lambda p:{'read_source':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
candidate=base/'boundary-candidates/P2OriginalCompactConcreteRun-rec-06.lean'
cb=candidate.read_bytes()
assert hashlib.sha256(cb).hexdigest()=='18f347ca0c231e7bcceca4e7752908bb311052b01495e839ffcef48aacd0ffd2'
original=base/'originals/P2OriginalCompactConcreteRun.lean'
ob=original.read_bytes()
payload=json.loads((base/'boundary-candidates/concrete-run-payload-06.json').read_bytes())
assert payload['candidate'].encode()==cb
back=cb
for patch in reversed(payload['definitionPatches']+payload['proofPatches']):
 assert back.count(patch['new'].encode())==1
 back=back.replace(patch['new'].encode(),patch['old'].encode())
assert back==ob
headers=lambda b:re.findall(r'^(?:private )?theorem\s+.*?(?=\s*:=)',b.decode(),re.M|re.S)
assert headers(ob)==headers(cb)
assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',cb.decode())
assert 'trace_state' not in cb.decode() and 'set_option pp.all' not in cb.decode()
items=[{'path':'ImbalancedChen/P2OriginalCompactConcreteRun.lean',**info(candidate),'git_blob':hashlib.sha1(b'blob '+str(len(cb)).encode()+b'\0'+cb).hexdigest()}]
items.append({'path':'docs/source-only/20261125-p24-original-compact/recursion-repairs/concrete-run/ConcreteRun-original.lean',**info(original)})
attempts=[
 ('attempt-001','P2OriginalCompactConcreteRun-rec-02.lean','7d9b2d444fbd4fe2b2aff1c04c350b0e'),
 ('attempt-002','P2OriginalCompactConcreteRun-rec-03.lean','43b123f21e31476d84feaf1da15fa337'),
 ('attempt-003','P2OriginalCompactConcreteRun-rec-04.lean','b7cdcbe771db4d179ad81957d8f61170'),
 ('attempt-004-goals','P2OriginalCompactConcreteRun-goals-01.lean','1ad23f540a8f4ca1bdb7765ff0643560'),
 ('attempt-005','P2OriginalCompactConcreteRun-rec-05.lean','818e765190b848bf8d6cdc288aebb002'),
 ('attempt-006','P2OriginalCompactConcreteRun-rec-06.lean','dd367ab8f2b643d5804840e840928551'),
]
for attempt,source_name,task in attempts:
 a=out/attempt;r=json.loads((a/'receipt.json').read_bytes());source=base/'boundary-candidates'/source_name;s=source.read_bytes()
 assert hashlib.sha256(s).hexdigest()==r['production_candidate_source']['sha256']
 isolated=b'import TreeFoldCandidate\n'+s
 assert len(isolated)==r['candidate_source']['bytes']
 assert hashlib.sha256(isolated).hexdigest()==r['candidate_source']['sha256']
 (a/'ConcreteRunCandidate.lean').write_bytes(isolated)
 assert hashlib.sha256(template).hexdigest()==r['template']['sha256']
 assert hashlib.sha256(audit).hexdigest()==r['audit_source']['sha256']
 (a/'OriginalAuditTemplate.lean').write_bytes(template);(a/'Audit.lean').write_bytes(audit)
 names=['status.json','task.log','receipt.json','compile.log','OriginalAuditTemplate.lean','Audit.lean','driver.py','run.sh','ConcreteRunCandidate.lean']
 if attempt=='attempt-002':names.append('run-expanded.sh')
 if attempt=='attempt-006':names.extend(['replay.log','audit.log'])
 for name in names:
  items.append({'path':f'docs/source-only/20261125-p24-original-compact/recursion-repairs/concrete-run/{attempt}/{name}',**info(a/name)})
 items.append({'path':f'docs/source-only/20261125-p24-original-compact/recursion-repairs/concrete-run/{attempt}/ConcreteRun-production-candidate.lean',**info(source)})
 assert all(r['postchecks'].values()) and not r['postcheck_errors']
 if attempt=='attempt-006':
  assert r['all_three_stages_passed']
 else:
  assert r['stages'][0]['exit_code']==1 and not r['stages'][0]['timed_out']
 # Confirm local raw logs remain exactly the remote receipt bytes.
 for stage in r['stages']:
  log=(a/(stage['stage']+'.log')).read_bytes()
  assert len(log)==stage['log']['bytes'] and hashlib.sha256(log).hexdigest()==stage['log']['sha256']
lines=(final/'audit.log').read_text().splitlines()
inventory=[json.loads(x.removeprefix('P0_QUEUE_INVENTORY ')) for x in lines if x.startswith('P0_QUEUE_INVENTORY ')]
declarations=[json.loads(x.removeprefix('P0_QUEUE_DECL ')) for x in lines if x.startswith('P0_QUEUE_DECL ')]
assert len(inventory)==1
names=[d['name'] for d in declarations]
assert len(names)==len(set(names))==receipt['audit_summary']['owned_count']
assert sorted(names)==sorted(inventory[0]['serialized'])==sorted(inventory[0]['environment'])
assert all(not d['unsafe'] and not d['partial'] and not d['axiom'] and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and '⋯' not in d['type'] for d in declarations)
review={
 'original_sha256':hashlib.sha256(ob).hexdigest(),'candidate_sha256':hashlib.sha256(cb).hexdigest(),
 'exact_inverse_to_original':True,'written_theorem_headers_equal':True,'written_theorem_count':len(headers(cb)),
 'definition_blocks_changed':5,'actual_failed_proof_blocks_changed':7,
 'all_other_bytes_identical':True,'production_imports_unchanged':True,'production_options_unchanged':True,
 'isolated_dependency_only':'TreeFoldCandidate; SHA-bound separately accepted 19-owned helper; production keeps original Ledger import',
 'root_cause_trace':'After dsimp only, zero Nat.rec remained in h; inner splitTreeAt was bound under the base lambda. Explicit change exposes the outer Option.map call before rewriting hs.',
 'independent_static_reviewer':'/root/p24_scope_audit (five recursors, seven proof directions, final map bridge, and exact final two p-to-parent substitutions)',
 'original_full_owned_count':len(names),'canonical_credit':False,'full_P2_credit':False,
}
(out/'review.json').write_text(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
extras=[
 (out/'review.json','review.json'),
 (base/'boundary-candidates/concrete-run-rec-06.patch','concrete-run-rec-06.patch'),
 (base/'boundary-candidates/concrete-run-rec-05-to-06.patch','concrete-run-rec-05-to-06.patch'),
 (out/'transport-rejection-02.json','transport-rejection-02.json'),
 (Path(__file__),'build-publication-manifest.py'),
]
for p,name in extras:
 items.append({'path':'docs/source-only/20261125-p24-original-compact/recursion-repairs/concrete-run/'+name,**info(p)})
manifest={
 'source_pin':'6e616f4e0372555f7a78bcdba3e198d0e277eec8',
 'status':'isolated candidate compile independent replay original full-owned PASS; five earlier failure/goal diagnostics retained',
 'tasks':{a:t for a,_,t in attempts},'canonical_credit':False,'full_P2_credit':False,
 'shared_fold_donor_files':receipt['shared_fold_donor_files'],
 'original_full_owned_count':len(names),'files':items,
}
target=out/'publication-manifest.json'
target.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'manifest':info(target),'file_count':len(items),'source':items[0],'owned_count':len(names),'header_count':len(headers(cb))},ensure_ascii=False))

