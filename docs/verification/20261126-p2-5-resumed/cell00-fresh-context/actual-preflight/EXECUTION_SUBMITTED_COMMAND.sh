python3 -B - <<'PY'
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path('/workspace/p25-q96-20261125')
pub='2106ae104bb98cd3d647a202df069b380e2de5bc'
runner=Path('/workspace/p25-four-consumers-v8-20261126.py')
runner_sha='ffcc4aff64705a29d9fa94faf44350753d4ba6faf2abbd0c748d634baf363beb'
selection_sha='1be717f81e2886e5291bdff7f129dbff8d75453656d6afa88c54cfd8168f01ca'
plan=Path('/workspace/p25-cell00-fresh-context-plan-20261126.log').read_bytes()
assert hashlib.sha256(plan).hexdigest()=='8e3b70331f8f1a996df9c4e63362250a1fbaadbaafcf2aa5629c645d0dae2208'
prefix='P25_V8_READ_ONLY_PLAN '
assert plan.decode().startswith(prefix)
p=json.loads(plan.decode()[len(prefix):])
assert p['publication_commit']==pub and p['runner_sha256']==runner_sha and p['selection_sha256']==selection_sha
assert p['writes_performed'] is False and p['normal_stages']==[] and p['available_objects']==31 and p['project_objects']==41
assert len(p['normal_rematerialization_order'])==10 and len(p['historical_archive_gaps'])==5 and p['runtime_pins']==15940
assert hashlib.sha256(runner.read_bytes()).hexdigest()==runner_sha
rc=subprocess.run([sys.executable,'-B',str(runner),pub,'--runner-sha256',runner_sha,'--selection-sha256',selection_sha,'--execute'],cwd=root).returncode
print('P25_V8_EXECUTION_PROCESS '+json.dumps({'exit_code':rc,'publication_commit':pub,'runner_sha256':runner_sha,'selection_sha256':selection_sha}),flush=True)
raise SystemExit(rc)
PY
