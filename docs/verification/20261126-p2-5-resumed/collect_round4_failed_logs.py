from pathlib import Path
import json,hashlib
root=Path('/workspace/p2-saving16-20261125')
out=root/'.lake/p25-followup-repairs-attempt004'
p=out/'RUN_RESULT.json';result=json.loads(p.read_text())
assert result['source_commit']=='168973571f795dbe8fb1c1bccfd7f7c54899b36a'
assert result['ended_utc'] and result['compile_summary']['total']==377
records=json.loads((root/'.lake/p2-private/records.json').read_text())
failed=['P4AOriginalFull87SourceDictionary','P4AOriginalH5H7SourceDispatch','P2OriginalFourthCapProducerInterface','P1OriginalHistoricalRetainedModulusLevel','P1OriginalCoarseFourthCellLimit','P4AActualEighthInheritedHistoryGuard']
for short in failed:
 module='ImbalancedChen.'+short;row=records[module];log=root/row['log']
 assert row['exit_code']!=0 and root.resolve() in log.resolve().parents
 raw=log.read_bytes()
 print(json.dumps({'module':module,'record':{k:row.get(k) for k in ['source','source_sha256','command','exit_code','seconds','log','closure_signature']},'log_bytes':len(raw),'log_sha256':hashlib.sha256(raw).hexdigest(),'log':raw.decode()},ensure_ascii=False),flush=True)
print(json.dumps({'result_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'result_full':result},ensure_ascii=False),flush=True)
