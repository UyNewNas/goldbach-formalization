set -euo pipefail
python3 -B - <<'PY'
from pathlib import Path
import hashlib,json,shutil,subprocess
project=Path.cwd()
assert str(project)=='/workspace/p2-7-20261125'
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()=='549ea2164c17a8a3f66edbbd88262ea9d5ef05f0'
manifest=project/'.lake/p2-private/exports/p27-complete-20261125/manifest.json'
assert hashlib.sha256(manifest.read_bytes()).hexdigest()=='73179a250532882aa5a945ba149fb734ee776dd3fdcef5d386af69b6303eca08'
assert not (project/'.lake/p27-delivery/attempt-001').exists(),'Do not repack an existing delivery'
disk=shutil.disk_usage(project)
print('P27_DELIVERY_PRECHECK',json.dumps({'independent_manifest_anchor':'73179a250532882aa5a945ba149fb734ee776dd3fdcef5d386af69b6303eca08','available_bytes':disk.free,'proof_credit':False}),flush=True)
assert disk.free>300000000,'Preserve existing exports; investigate capacity before packing'
PY
git fetch --no-tags origin ca15b1035ac8fc9be746fe8108f532f73aaaff2d
git checkout --detach ca15b1035ac8fc9be746fe8108f532f73aaaff2d
python3 -B - <<'PY'
from pathlib import Path
import hashlib,json,subprocess
project=Path.cwd()
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert head=='ca15b1035ac8fc9be746fe8108f532f73aaaff2d'
manifest=json.loads((project/'docs/p2/20261125/p27/source-manifest.json').read_text())
assert len(manifest['files'])==manifest['project_module_count']==81
for name,row in manifest['files'].items():
    raw=(project/row['path']).read_bytes()
    assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],name
for relative,expected in {
 'docs/p2/20261125/p27/prepare-delta-evidence.sh':'ba82e34827a01c234bc13e0fb09c50c32841e2d703f43bad1c2b4cd9c42935ff',
 'docs/p2/20261125/p27/next-private-step.sh':'d9732b5dd86b8ac06d171ba6ebeb9b0ff8946734d716e7a7bebcc2143dce5132',
 'verification/part2/p27_delta_evidence.py':'f4ddcb99b81da3718955973573eddbdd398d82ee7064e093f0a0c7859ae46604',
}.items():
    assert hashlib.sha256((project/relative).read_bytes()).hexdigest()==expected,relative
relative='docs/source-only/20261113-resume/coherent-cache-tools/checkpoint_original_protocol.py'
raw=subprocess.check_output(['git','show','549ea2164c17a8a3f66edbbd88262ea9d5ef05f0:'+relative])
assert len(raw)==1766 and hashlib.sha256(raw).hexdigest()=='cfcb50064a13632a4a0fa8372d27bf86dd91f92eb6c38482afa575cf34921aff'
destination=project/relative
assert not destination.is_symlink() and destination.resolve()==destination,'Original protocol path redirected'
existed=destination.exists()
if existed:
    assert destination.is_file() and destination.read_bytes()==raw,'Existing protocol differs'
else:
    destination.parent.mkdir(parents=True,exist_ok=True)
    with destination.open('xb') as output:
        output.write(raw)
assert destination.read_bytes()==raw
print('P27_DELIVERY_SOURCE_AND_TOOL_BYTES_VERIFIED',json.dumps({'git_head':head,'source_modules':81,'original_protocol_bytes':len(raw),'original_protocol_existed':existed,'proof_credit':False}),flush=True)
PY
bash docs/p2/20261125/p27/next-private-step.sh 0
