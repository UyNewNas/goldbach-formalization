set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
cd /workspace/p2-4-compact-proof-20261125
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'PY'
from pathlib import Path
import hashlib,json,sys,os,subprocess,shutil
root=Path.cwd();pin="6e616f4e0372555f7a78bcdba3e198d0e277eec8"
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==pin
assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],text=True).strip()
def digest(p):
 with Path(p).open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()
out=root/".lake/p24-audit-export/source6e-full324-preflight-001"
manifest_path=out/"manifest.json";manifest_sha="7a99f246b4c8bc54bc55ce3497de1445a270d76a34ce6af0a2e1b8e1f5e1e934"
assert digest(manifest_path)==manifest_sha
manifest=json.loads(manifest_path.read_bytes())
original_package=manifest["packages"][0]
assert len(manifest["packages"])==1 and original_package["bytes"]==581735403 and original_package["sha256"]=="3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463"
src=out/"all.tar.gz"
assert src.is_symlink() and not src.exists()
exporter=root/"verification/part2/export_winner9_private_evidence.py"
assert digest(exporter)=="fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645"
sys.path.insert(0,str(exporter.parent))
import export_winner9_private_evidence as original
registry=root/".lake/p2-private/records.json";registry_raw=registry.read_bytes()
assert hashlib.sha256(registry_raw).hexdigest()==manifest["records_snapshot_sha256"]
records=json.loads(registry_raw)
metadata={k:v for k,v in manifest.items() if k not in ("packages","files")}
synthetic={
 "EXPORT_METADATA.json":original.encoded(metadata),
 "context/selected-compile-records.json":original.encoded({name:records[name] for name in sorted(manifest["object_manifest"])})
}
evidence=original.Evidence()
for name,entry in manifest["files"].items():
 if name in synthetic:
  raw=synthetic[name]
 else:
  origin=Path(entry["origin"])
  assert origin.is_absolute() and origin.is_file(),(name,"missing frozen origin",str(origin))
  raw=origin.read_bytes()
  evidence.frozen[origin]=entry["sha256"]
 assert len(raw)==entry["bytes"] and hashlib.sha256(raw).hexdigest()==entry["sha256"],(name,"original byte binding mismatch")
 evidence.add_bytes(name,raw,entry["origin"],entry["role"])
assert evidence.file_index()==manifest["files"]
evidence.verify_frozen()
print(json.dumps({"phase":"all_original_members_verified","files":len(evidence.files),"member_bytes":sum(v["bytes"] for v in evidence.files.values()),"manifest_sha256":manifest_sha}),flush=True)
recovery=out/"recovery-exact-001"
recovery.mkdir(exist_ok=False)
assert shutil.disk_usage(root).free>original_package["bytes"]+16777216
recovered=original.package(recovery/"all.tar.gz",set(evidence.files),original_package["modules"],evidence,manifest["transfer_page_bytes"])
assert recovered["bytes"]==original_package["bytes"] and recovered["sha256"]==original_package["sha256"]
assert recovered["uncompressed_payload_bytes"]==original_package["uncompressed_payload_bytes"]
evidence.verify_frozen()
assert digest(manifest_path)==manifest_sha
assert hashlib.sha256(registry.read_bytes()).hexdigest()==manifest["records_snapshot_sha256"]
os.replace(recovery/"all.tar.gz",src)
assert src.is_file() and not src.is_symlink() and digest(src)==original_package["sha256"]
receipt={"action":"exact_archive_reconstruction_after_task_private_tmp_did_not_persist",
 "source_pin":pin,"original_package":str(src),"bytes":src.stat().st_size,"sha256":digest(src),
 "exact_original_archive_bytes_restored":True,"original_manifest_unchanged":True,
 "original_member_bindings_verified":len(evidence.files),"original_exporter_package_function_used":True,
 "original_source_object_audit_native_files_unchanged":True,
 "records_snapshot_sha256":manifest["records_snapshot_sha256"],
 "persistent_workspace_free_bytes":shutil.disk_usage(root).free,"full_P2_complete":False}
(out/"exact-archive-recovery.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps(receipt),flush=True)
PY
