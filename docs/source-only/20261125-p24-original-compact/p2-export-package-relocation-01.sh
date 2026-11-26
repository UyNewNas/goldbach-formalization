set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
cd /workspace/p2-4-compact-proof-20261125
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'PY'
from pathlib import Path
import hashlib,json,os,shutil,subprocess
root=Path.cwd();pin="6e616f4e0372555f7a78bcdba3e198d0e277eec8"
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==pin
def digest(p):
 with Path(p).open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()
src=root/".lake/p24-audit-export/source6e-full324-preflight-001/all.tar.gz"
manifest=src.parent/"manifest.json";manifest_sha="7a99f246b4c8bc54bc55ce3497de1445a270d76a34ce6af0a2e1b8e1f5e1e934"
expected="3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463";size=581735403
assert manifest.stat().st_size==11997843 and digest(manifest)==manifest_sha
assert not src.is_symlink() and src.stat().st_size==size and digest(src)==expected
dst=Path("/tmp/p24-audit-export-preserved-20261126/source6e-full324-preflight-001/all.tar.gz")
assert not dst.exists() and not dst.with_suffix(".gz.part").exists()
assert Path("/tmp").stat().st_dev!=root.stat().st_dev
assert shutil.disk_usage("/tmp").free>size+67108864
before=shutil.disk_usage(root).free
registry=root/".lake/p2-private/records.json";registry_sha=digest(registry)
dst.parent.mkdir(parents=True,exist_ok=False);temp=dst.with_suffix(".gz.part")
with src.open("rb") as f, temp.open("xb") as g:
 shutil.copyfileobj(f,g,1048576);g.flush();os.fsync(g.fileno())
assert temp.stat().st_size==size and digest(temp)==expected
assert src.stat().st_size==size and digest(src)==expected
temp.rename(dst)
src.unlink()
src.symlink_to(dst)
assert src.stat().st_size==size and digest(src)==expected
assert digest(manifest)==manifest_sha and digest(registry)==registry_sha
record={"action":"relocate_exact_completed_export_package_and_preserve_original_path_symlink",
 "source_pin":pin,"original_path":str(src),"preserved_path":str(dst),"bytes":size,"sha256":expected,
 "original_path_readable_with_same_bytes":True,"independent_tmp_filesystem":True,
 "manifest_unchanged_sha256":manifest_sha,"registry_unchanged_sha256":registry_sha,
 "workspace_free_bytes_before":before,"workspace_free_bytes_after":shutil.disk_usage(root).free,
 "no_source_object_audit_native_or_other_task_files_changed":True,"full_P2_complete":False}
(src.parent/"package-relocation.json").write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps(record),flush=True)
flags=Path("/tmp/p24-owned-flags-preflight-20261126/attempt-001/owned-flags.log")
if flags.exists():
 b=flags.read_bytes()
 print(json.dumps({"artifact":"flags_diagnostic_failure_log","path":str(flags),"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest(),"text":b.decode()}),flush=True)
m=json.loads(manifest.read_text())
print(json.dumps({"artifact":"preflight_export_largest_members","file_count":len(m["files"]),
 "total_member_bytes":sum(v["bytes"] for v in m["files"].values()),
 "largest":[{"name":k,"bytes":v["bytes"],"origin":v["origin"]} for k,v in sorted(m["files"].items(),key=lambda kv:kv[1]["bytes"],reverse=True)[:12]]}),flush=True)
PY
