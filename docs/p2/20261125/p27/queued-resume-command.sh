set -euo pipefail
p27_refresh () {
  local p27_fetched=0
  for p27_attempt in 1 2 3; do
    if git fetch --no-tags origin work/p2-7-formal-proof-20261125; then p27_fetched=1; break; fi
    sleep 15
  done
  test "$p27_fetched" = 1
  git checkout --detach FETCH_HEAD
  git rev-parse HEAD
}
p27_refresh
python3 verification/part2/run_winner9_private_checks.py ImbalancedChen.P2AdoptedRowsActualEnclosure ImbalancedChen.Certificates.P2PairedSupportFubini ImbalancedChen.Certificates.P2ContinuousFibreFubini --workers 1 --threads 1 --memory-mb 12288 --time-budget-seconds 600
mapfile -t p27_numeric_targets < <(head -n 19 docs/p2/20261125/p27/audit-targets.txt)
LEAN_NUM_THREADS=1 python3 verification/part2/run_winner9_private_audit.py --memory-mb 11264 --summary-name p27-numeric-fubini-summary.json "${p27_numeric_targets[@]}"
p27_refresh
test -f verification/part2/adopt_p27_currentchen_cache.py
python3 - <<'PY'
from pathlib import Path,PurePosixPath
import hashlib,tarfile,subprocess,json
project=Path.cwd()
protocol='docs/source-only/20261113-resume/coherent-cache-tools/checkpoint_original_protocol.py'
raw=subprocess.check_output(['git','show','HEAD:'+protocol])
assert hashlib.sha256(raw).hexdigest()=='cfcb50064a13632a4a0fa8372d27bf86dd91f92eb6c38482afa575cf34921aff'
dest=project/protocol
dest.parent.mkdir(parents=True,exist_ok=True)
if dest.exists(): assert dest.read_bytes()==raw
else:
 with dest.open('xb') as f: f.write(raw)
for name,expected,dirname in [
 ('native-inputs.tar.xz','25a5b45cf649c8b97df57e6a1dcac71c7f22d5ccd5ab2bf92eda399aeff9ffba','native'),
 ('currentchen-inputs.tar.xz','7308d5b143841734f94b95c7d4499f71110a206ffacf4374f101ef8633ab04eb','currentchen')]:
 archive=project/'docs/p2/20261125/p27'/name
 assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected,name
 dest=project/'.lake/p27-inputs'/dirname
 dest.mkdir(parents=True,exist_ok=True)
 assert not dest.is_symlink()
 with tarfile.open(archive,'r:xz') as t:
  members=t.getmembers()
  assert len({m.name for m in members})==len(members)
  for m in members:
   rel=PurePosixPath(m.name)
   assert m.isfile() and not rel.is_absolute() and '..' not in rel.parts
   assert rel.parts==('MANIFEST.json',) or (len(rel.parts)==2 and rel.parts[0]=='objects')
   p=dest/rel
   p.parent.mkdir(parents=True,exist_ok=True)
   assert not p.is_symlink() and not p.parent.is_symlink()
   data=t.extractfile(m).read()
   if p.exists(): assert p.read_bytes()==data
   else:
    with p.open('xb') as f: f.write(data)
 print('P27_VERIFIED_INPUT_TRANSPORT',json.dumps({'archive':name,'sha256':expected,'members':len(members),'destination':str(dest)}),flush=True)
PY
python3 -B verification/part2/p27_qualify_native_inputs.py --project-root /workspace/p2-7-20261125 --base-snapshot /workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json --bundle /workspace/p2-7-20261125/.lake/p27-inputs/native --out /workspace/p2-7-20261125/.lake/p27-native/attempt-001
python3 -B verification/part2/adopt_p27_currentchen_cache.py --project-root /workspace/p2-7-20261125 --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-001/EXTERNAL_SNAPSHOT.json --native-bundle /workspace/p2-7-20261125/.lake/p27-inputs/native --project-bundle /workspace/p2-7-20261125/.lake/p27-inputs/currentchen --out /workspace/p2-7-20261125/.lake/p27-currentchen-adoption/attempt-001
python3 verification/part2/run_winner9_private_checks.py ImbalancedChen.P2PairedCertificateCompletion --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-001/EXTERNAL_SNAPSHOT.json --workers 1 --threads 1 --memory-mb 12288 --time-budget-seconds 900
mapfile -t p27_all_targets < docs/p2/20261125/p27/audit-targets.txt
LEAN_NUM_THREADS=1 python3 verification/part2/run_winner9_private_audit.py --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-001/EXTERNAL_SNAPSHOT.json --memory-mb 11264 --summary-name p27-complete-summary.json "${p27_all_targets[@]}"
python3 - <<'PY'
from pathlib import Path
import hashlib,subprocess
out=Path('.lake/p27-repro-drivers')
out.mkdir(exist_ok=True)
for path,sha in [
 ('docs/verification/20261124-p2-private/driver-v1.py','05f31ad7f78c69bf58a1f0daab4b597db9a90190f255a880abdab22767c864b5'),
 ('docs/verification/20261124-p2-private/audit-driver-v2.py','b214fe826d40f96c9907cb9c42f0ac96dcc9bc48dc080a264c9c13de2b43cc08')]:
 raw=subprocess.check_output(['git','show','HEAD:'+path])
 assert hashlib.sha256(raw).hexdigest()==sha
 target=out/Path(path).name
 if target.exists(): assert target.read_bytes()==raw
 else:
  with target.open('xb') as f: f.write(raw)
PY
python3 verification/part2/export_winner9_private_evidence.py --output-dir .lake/p2-private/exports/p27-complete-20261125 --split all --transfer-page-bytes 1000000 --driver-file .lake/p27-repro-drivers/driver-v1.py --driver-file .lake/p27-repro-drivers/audit-driver-v2.py --extra-evidence docs/p2/20261125/p27 "${p27_all_targets[@]}"
