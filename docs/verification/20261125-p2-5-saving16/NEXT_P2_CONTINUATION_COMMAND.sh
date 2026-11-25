set -euo pipefail
python3 - <<'PY'
from pathlib import Path
import hashlib, json, shutil, subprocess, sys, datetime
root=Path.cwd()
base='860575ac51b6218f2cc235efb0b5fe40d1e625b9'
branch='refs/heads/work/p2-5-saving16-20261125'
if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],text=True).strip():
    raise SystemExit('Refusing to alter an unexpectedly dirty tracked worktree')
subprocess.check_call(['git','fetch','origin',branch])
resolved=subprocess.check_output(['git','rev-parse','FETCH_HEAD'],text=True).strip()
subprocess.check_call(['git','merge-base','--is-ancestor',base,resolved])
subprocess.check_call(['git','merge','--ff-only',resolved])
if subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()!=resolved:
    raise SystemExit('Resolved source HEAD mismatch')
receipt={'source_commit':resolved,'source_tree':subprocess.check_output(['git','rev-parse','HEAD^{tree}'],text=True).strip(),'minimum_reviewed_commit':base,'resolved_once_at_start':True,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'disk_free_start':shutil.disk_usage(root).free}
Path('.lake/p25-next-run-source.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('P25_FROZEN_SOURCE '+json.dumps(receipt),flush=True)
folder=Path('docs/verification/20261125-p2-5-saving16')
graph=json.loads((folder/'CONTINUATION_SOURCE_CLOSURE.json').read_text())
for name,entry in graph['modules'].items():
    if hashlib.sha256(Path(entry['source']).read_bytes()).hexdigest()!=entry['sha256']:
        raise SystemExit('Published source graph differs at '+name)
input_log=Path('.lake/p25-q96-input-preparation.log')
with input_log.open('w') as stream:
    inputs_rc=subprocess.call([sys.executable,str(folder/'prepare-q96-original-inputs.py')],stdout=stream,stderr=subprocess.STDOUT)
print('P25_INPUT_PREPARATION_EXIT',inputs_rc,flush=True)
print(input_log.read_text(),flush=True)
snapshot='/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json'
compile_cmd=[sys.executable,'verification/part2/run_winner9_private_checks.py',*graph['roots'],'--workers','1','--threads','1','--memory-mb','11264','--external-snapshot',snapshot,'--time-budget-seconds','1400']
compile_rc=subprocess.call(compile_cmd)
targets=json.loads((folder/'CONTINUATION_AUDIT_TARGETS.json').read_text())['modules']
priority=['ImbalancedChen.P2Saving16NegativeFiniteCore','ImbalancedChen.P2Saving16FourteenNegativeFibrePartition','ImbalancedChen.P2Saving16Full87IntegralIdentity','ImbalancedChen.P2OriginalSaving16JensenFloor','ImbalancedChen.P2OriginalAffineSimplexGeometry','ImbalancedChen.P2OriginalSaving19SourceJson']
ordered=[x for x in priority if x in targets]+[x for x in targets if x not in priority]
# The existing audit verifies every current source/object/dependency record;
# incomplete or failed compilation cannot grant audit acceptance.
audit_rc=subprocess.call([sys.executable,'verification/part2/run_winner9_private_audit.py',*ordered,'--summary-name','p25-continuation-owned-audit.json','--memory-mb','11264','--external-snapshot',snapshot])
receipt.update({'input_preparation_exit':inputs_rc,'compile_exit':compile_rc,'audit_exit':audit_rc,'audit_requested_modules':len(ordered),'disk_free_end':shutil.disk_usage(root).free,'ended_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
Path('.lake/p25-next-run-source.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('P25_CONTINUATION_RESULT '+json.dumps(receipt),flush=True)
sys.exit(int(any((inputs_rc,compile_rc,audit_rc))))
PY
