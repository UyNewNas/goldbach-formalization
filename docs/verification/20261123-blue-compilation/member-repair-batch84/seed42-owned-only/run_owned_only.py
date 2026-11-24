from pathlib import Path
import json,hashlib,datetime,subprocess,time,re
R=Path(__file__).resolve().parent;P=Path('/workspace/blue-member-build');S=Path('/workspace/blue-build-tools/runtime-evidence/state.json');M='ImbalancedChen.P2Winner9CompleteSeedBlock42';short=M.split('.')[-1]
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,d):assert not p.exists();p.write_text(json.dumps(d,indent=2)+'\n')
lane=json.loads((R/'VALIDATION_LANE.json').read_text());assert lane['status']=='VALIDATION_LANE_ACQUIRED' and Path(lane['state'])==S
normal=R.parent/(short+'-normal-command.json');kernel=R.parent/(short+'-kernel-command.json');assert json.loads(normal.read_text())['exit_code']==0 and json.loads(kernel.read_text())['exit_code']==0
snap=json.loads((R.parent/(short+'-AFTER_KERNEL.json')).read_text());assert len(snap)==6
for rel,d in snap.items():assert (P/rel).stat().st_size==d['bytes'] and sha(P/rel)==d['sha256']
write(R/'SOURCE_PLUS_FIVE_BEFORE.json',snap);state=json.loads(S.read_text());journal=Path(state['log']);start_offset=journal.stat().st_size
argv=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(S),'lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--root='+str(R),str(R/'OwnedOnlyAudit.lean')];start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
with (R/'audit.log').open('x') as out:result=subprocess.run(argv,cwd=P,stdout=out,stderr=subprocess.STDOUT)
rec={'argv':argv,'cwd':str(P),'started_utc':start,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'exit_code':result.returncode,'log_sha256':sha(R/'audit.log'),'no_original_module_normal_or_kernel_invocations':True};write(R/'AUDIT_COMMAND.json',rec);assert result.returncode==0
end_offset=journal.stat().st_size
with journal.open('rb') as f:f.seek(start_offset);tail=f.read(end_offset-start_offset)
(R/'ACTUAL_GUARD_JOURNAL_TAIL.jsonl').write_bytes(tail);events=[json.loads(l) for l in tail.splitlines()];actual=[x for x in events if str(R/'OwnedOnlyAudit.lean') in x.get('command',[])];assert len(actual)==1;cmd=actual[0]['command'];assert all(x in cmd for x in ['-t0','-j2','-M12288','maxRecDepth=100000','maxHeartbeats=4000000']);write(R/'ACTUAL_AUDIT_RUNTIME.json',{'state':str(S),'state_sha256':sha(S),'journal':str(journal),'before_byte_offset':start_offset,'after_byte_offset':end_offset,'captured_tail_sha256':sha(R/'ACTUAL_GUARD_JOURNAL_TAIL.jsonl'),'actual_runtime':actual[0]})
text=(R/'audit.log').read_text();records=[json.loads(x) for x in re.findall(r'AUDIT_RECORD (\{[^\n]+\})',text)];inventories=[json.loads(x) for x in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})',text)];assert len(inventories)==1;names=inventories[0]['names'];assert len(names)==len(records) and set(names)=={x['name'] for x in records} and {x['module'] for x in records}=={M};assert not any(x['kind']=='axiom' or not set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in records);assert not any(t in text for t in ['sorryAx','…','⋯','...'])
for rel,d in snap.items():assert (P/rel).stat().st_size==d['bytes'] and sha(P/rel)==d['sha256']
write(R/'OWNED_EXPORTS.json',records);write(R/'PUBLIC_EXPORTS.json',[x for x in records if not x['is_private']]);write(R/'SEED42_COMPLETE_OWNED_SUPPLEMENT_RESULT.json',{'status':'PASS_CURRENT_SEED42_NORMAL_KERNEL_AND_COMPLETE_OWNED_WITH_NO_NORMAL_KERNEL_REPETITION','module':M,'source_sha256':snap[M.replace('.','/')+'.lean']['sha256'],'owned_total':len(records),'public_total':sum(not x['is_private'] for x in records),'private_total':sum(x['is_private'] for x in records),'full_type_AST_universe_and_std3_axioms':True,'normal_receipt_sha256':sha(normal),'kernel_receipt_sha256':sha(kernel),'actual_audit_command':rec,'source_plus_five_outputs_stable':True,'archive_not_accepted_by_this_leaf_supplement':True});print('SEED42_FULL_OWNED_PASS',len(records),flush=True)
