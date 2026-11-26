python3 -B - <<'PY'
from pathlib import Path
import os,json
paths=[
"/workspace/p2-4-compact-proof-20261125/.lake/p24-audit-export/source6e-full324-preflight-001/all.tar.gz",
"/tmp/p24-audit-export-preserved-20261126/source6e-full324-preflight-001/all.tar.gz",
"/tmp/p24-owned-flags-preflight-20261126/attempt-001/owned-flags.log"]
for value in paths:
 p=Path(value);r={"path":value,"lexists":os.path.lexists(p),"exists":p.exists(),"symlink":p.is_symlink()}
 if p.is_symlink():r["target"]=os.readlink(p)
 if p.exists():r.update({"bytes":p.stat().st_size,"device":p.stat().st_dev})
 print(json.dumps(r),flush=True)
print(json.dumps({"tmp_device":Path("/tmp").stat().st_dev,"workspace_device":Path("/workspace").stat().st_dev}))
PY
