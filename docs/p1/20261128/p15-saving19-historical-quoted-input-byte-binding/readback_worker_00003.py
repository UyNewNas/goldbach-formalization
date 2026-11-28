from pathlib import Path
import json,hashlib,subprocess,datetime,filecmp,os,signal
ROOT=Path(__file__).resolve().parent
ATTEMPT=ROOT/'readback-00003'
ATTEMPT.mkdir(exist_ok=False)
def fp(p):
 p=Path(p)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest())
def save(name,data):(ATTEMPT/name).write_text(json.dumps(data,indent=2)+'\n')
records=[]
for name in ['ReadQuotedInputsAudit_00003.lean','readback_worker_00003.py','EXPECTED_CURRENT_INPUTS.json','ORIGINAL_ACCEPTED_OWNERS.json']:
 records.append(fp(ROOT/name))
for owner in json.loads((ROOT/'ORIGINAL_ACCEPTED_OWNERS.json').read_text())['owners']:
 receipt_fp=fp(owner['receipt']);assert receipt_fp['sha256']==owner['receipt_sha256'];records.append(receipt_fp)
 for rel,wanted in owner['source_and_five_outputs'].items():
  got=fp(Path('/workspace/blue-member-build')/rel);assert {k:got[k] for k in ['bytes','sha256']}==wanted;records.append(got)
expected=json.loads((ROOT/'EXPECTED_CURRENT_INPUTS.json').read_text())['expected_original_inputs']
for wanted in expected:
 got=fp(wanted['path']);assert {k:got[k] for k in ['bytes','sha256']}=={k:wanted[k] for k in ['bytes','sha256']};records.append(got)
save('INPUTS_BEFORE.json',records)
(ATTEMPT/'EXECUTED_READER.lean').write_bytes((ROOT/'ReadQuotedInputsAudit_00003.lean').read_bytes())
(ATTEMPT/'EXECUTED_WORKER.py').write_bytes(Path(__file__).read_bytes())
command=['lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000',str(ROOT/'ReadQuotedInputsAudit_00003.lean')]
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (ATTEMPT/'readback.log').open('w') as log:
 proc=subprocess.Popen(command,cwd='/workspace/blue-member-build',stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 try:
  returncode=proc.wait(timeout=1800)
 except subprocess.TimeoutExpired:
  # Only this newly-created IO helper process group; never an existing compiler/service.
  os.killpg(proc.pid,signal.SIGTERM)
  try:proc.wait(timeout=5)
  except subprocess.TimeoutExpired:
   os.killpg(proc.pid,signal.SIGKILL);proc.wait()
  raise
 result=subprocess.CompletedProcess(command,returncode)
save('COMMAND.json',dict(argv=command,cwd='/workspace/blue-member-build',started_utc=started,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=result.returncode,log=fp(ATTEMPT/'readback.log'),purpose='Normal compile-time metadata audit reading serialized definition Expr only; zero old proof/kernel replay; not mathematical acceptance'))
after=[fp(x['path']) for x in records];save('INPUTS_AFTER.json',after);assert after==records
if result.returncode:raise SystemExit(result.returncode)
rows=[]
for i in range(13):
 for kind,filename in [('Geometry',f'eighth-third-minorant-extension-20261009-a23-s23_low-{i:02d}-cell.witness.json'),('Moment',f'eighth-third-moment-refinement-20261009-a23-low-{i:02d}.witness.json')]:
  actual=ATTEMPT/'decoded'/f'{kind}{i:02d}.json';original=Path('/workspace/goldbach-research')/filename
  assert filecmp.cmp(actual,original,shallow=False),str(original)
  rows.append(dict(current_original=fp(original),decoded_historical_quoted_input=fp(actual),full_bytewise_equal=True))
save('READBACK_RESULTS.json',dict(status='PASS_READ_ONLY_HISTORICAL_QUOTE_BYTEWISE_READBACK',rows=rows,files=26,total_bytes=sum(x['current_original']['bytes'] for x in rows),all_inputs_before_after_identical=True,raw_source_and_artifact_fingerprints_pinned=True,new_Lean_compiletime_metadata_audit_commands=1,old_normal_kernel_or_audit_replay_commands=0,new_mathematical_credit=0,concrete_parse_success_shapes_numerics_ownership_not_claimed=True,whole_P1_4_complete=False,whole_P1_5_complete=False))
print('PASS_READ_ONLY_QUOTED_INPUT_BYTES',len(rows))
