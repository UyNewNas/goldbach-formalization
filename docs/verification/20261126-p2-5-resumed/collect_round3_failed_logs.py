from pathlib import Path
import json, hashlib, subprocess
root=Path('/workspace/p2-saving16-20261125')
out=root/'.lake/p25-followup-repairs-attempt003'
result=json.loads((out/'RUN_RESULT.json').read_text())
assert result['source_commit']=='6a4bfce285e1512b3ba31fb408812040b8aee368'
assert result['ended_utc'] and result['compile_summary']['total']==377
records=json.loads((root/'.lake/p2-private/records.json').read_text())
failed=['P4AOriginalFirstFailureH3SourceSemantics','P4AOriginalH5H7SourceDispatch','P2OriginalFourthCapProducerInterface','P1OriginalHistoricalPhysicalCoefficient','P1OriginalCoarseFourthCellIntegral','P5OriginalAdoptedEighthPhysicalMasks','P4AActualEighthInheritedHistoryGuard','P2OriginalAffineSimplexGeometry']
for short in failed:
    module='ImbalancedChen.'+short
    row=records[module]
    p=root/row['log']
    assert row['exit_code']!=0 and root.resolve() in p.resolve().parents
    raw=p.read_bytes()
    print(json.dumps({'module':module,'record':{k:row.get(k) for k in ['source','source_sha256','command','exit_code','seconds','log','closure_signature']},'log_bytes':len(raw),'log_sha256':hashlib.sha256(raw).hexdigest(),'log':raw.decode()},ensure_ascii=False),flush=True)
print(json.dumps({'result_sha256':hashlib.sha256((out/'RUN_RESULT.json').read_bytes()).hexdigest(),'source_commit':result['source_commit'],'compile_summary':result['compile_summary'],'audit_summary':result['audit_summary']},ensure_ascii=False),flush=True)

