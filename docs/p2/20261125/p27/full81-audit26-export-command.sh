set -euo pipefail
python3 -B - <<'PY'
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,'verification/part2')
from run_winner9_private_audit import project_nodes,snapshot,verify_compilation
from run_winner9_private_checks import LEAN,MATHLIB,PIN
from winner9_external_snapshot import ExternalSnapshot,mark_project_nodes
root=Path.cwd();lib=root/'.lake/p2-private/lib'
assert str(root)=='/workspace/p2-7-20261125'
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert head=='549ea2164c17a8a3f66edbbd88262ea9d5ef05f0','Candidate changed; require a new explicitly reviewed continuation'
print('P27_ACTUAL_FINAL_CHECK_SOURCE',head,flush=True)
manifest=json.loads(Path('docs/p2/20261125/p27/source-manifest.json').read_text())
assert len(manifest['files'])==manifest['project_module_count']==81
for name,row in manifest['files'].items():
 raw=Path(row['path']).read_bytes()
 assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],name
receipt_path=root/'.lake/p2-private/native-record-migration/attempt-003/RECORD_REBIND.json'
raw=receipt_path.read_bytes();receipt=json.loads(raw);receipt_sha=hashlib.sha256(raw).hexdigest()
assert receipt['status']=='EQUIVALENCE_VERIFIED_FOR_REGISTRY_CAS'
assert receipt['original_registry']['external_anchor']=='f91d99533ee30ec2ced9b25d9c980804930787e7741f51b56a3668ac11631b48'
assert receipt['original_capture_manifest']['sha256']=='d078c02618aa11821055ad4cebeeb815474f41a64a252c6a3abf4c20fce978e7'
rebound=['ImbalancedChen.CurrentPairedBuchstabBridge','ImbalancedChen.Certificates.PairedV2FullBuchstab']
assert receipt['rebound']==rebound and receipt['retained']==['ImbalancedChen.Certificates.PairedV2']
records=json.loads((root/'.lake/p2-private/records.json').read_text())
for name in rebound:
 assert records[name]['historical_cache_qualification']=={'path':str(receipt_path),'sha256':receipt_sha}
 assert records[name]['closure_signature']==receipt['proposed_closure_signatures'][name]
all_nodes=project_nodes(root,'ImbalancedChen.P2PairedCertificateCompletion')
pending={'ImbalancedChen.P2PairedFibreBuchstabVariableLower','ImbalancedChen.P2PairedSemanticGainEnclosure','ImbalancedChen.Certificates.P2SemanticGainSetIntegral','ImbalancedChen.P2PairedCertificateCompletion'}
assert len(all_nodes)==81 and pending<=set(all_nodes)
nodes={name:node for name,node in all_nodes.items() if name not in pending}
assert len(nodes)==77 and all(set(node['deps'])<=set(nodes) for node in nodes.values())
toolchain=records[next(iter(nodes))]['toolchain']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=MATHLIB,text=True).strip()==PIN
assert subprocess.check_output([LEAN,'--version'],text=True).strip()==toolchain['lean_version']
external=ExternalSnapshot(root/'.lake/p27-native/attempt-003/EXTERNAL_SNAPSHOT.json',lean=LEAN,mathlib_pin=PIN,project_lib=lib)
mark_project_nodes(nodes,set(external.modules))
frozen=snapshot(root,lib,nodes,toolchain,external)
verify_compilation(records,nodes,frozen)
print('P27_ALL_77_EXISTING_CACHES_VERIFIED_BEFORE_SOURCE_COMPILATION',json.dumps({'cached_modules':77,'uncompiled_targets':sorted(pending),'rebind_receipt_sha256':receipt_sha,'mathematical_credit_added':False}),flush=True)
PY
python3 -B verification/part2/run_winner9_private_checks.py ImbalancedChen.P2PairedCertificateCompletion --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-003/EXTERNAL_SNAPSHOT.json --workers 1 --threads 1 --memory-mb 12288 --time-budget-seconds 900
mapfile -t p27_all_targets < docs/p2/20261125/p27/audit-targets.txt
test "${#p27_all_targets[@]}" = 26
LEAN_NUM_THREADS=1 python3 -B verification/part2/run_winner9_private_audit.py --external-snapshot /workspace/p2-7-20261125/.lake/p27-native/attempt-003/EXTERNAL_SNAPSHOT.json --memory-mb 11264 --summary-name p27-complete-summary.json "${p27_all_targets[@]}"
python3 -B - <<'PY'
from pathlib import Path
import hashlib,subprocess,json,shutil
out=Path('.lake/p27-repro-drivers');out.mkdir(exist_ok=True)
for path,sha in [('docs/verification/20261124-p2-private/driver-v1.py','05f31ad7f78c69bf58a1f0daab4b597db9a90190f255a880abdab22767c864b5'),('docs/verification/20261124-p2-private/audit-driver-v2.py','b214fe826d40f96c9907cb9c42f0ac96dcc9bc48dc080a264c9c13de2b43cc08')]:
 raw=subprocess.check_output(['git','show','HEAD:'+path]);assert hashlib.sha256(raw).hexdigest()==sha
 target=out/Path(path).name
 assert not target.is_symlink()
 if target.exists(): assert target.read_bytes()==raw
 else:
  with target.open('xb') as stream: stream.write(raw)
print('P27_FIRST_FULL_EXPORT_DISK',json.dumps(shutil.disk_usage(Path.cwd())._asdict()),flush=True)
assert shutil.disk_usage(Path.cwd()).free>750000000,'Preserve accepted evidence; insufficient first-export headroom'
assert not Path('.lake/p2-private/exports/p27-complete-20261125').exists(),'First export already exists; inspect and reuse it'
PY
python3 -B verification/part2/export_winner9_private_evidence.py --output-dir .lake/p2-private/exports/p27-complete-20261125 --split all --transfer-page-bytes 1000000 --driver-file .lake/p27-repro-drivers/driver-v1.py --driver-file .lake/p27-repro-drivers/audit-driver-v2.py --extra-evidence docs/p2/20261125/p27 "${p27_all_targets[@]}"


