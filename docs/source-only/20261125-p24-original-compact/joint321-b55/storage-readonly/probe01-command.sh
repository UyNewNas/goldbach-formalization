set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
python3 -B - <<'P24_READ_ONLY_STORAGE_INVENTORY'
from pathlib import Path
import hashlib,json,os,stat,subprocess,time
started=time.monotonic()
ws=Path("/workspace")
project=ws/"p2-4-compact-proof-20261125"
roots=sorted(p for p in ws.iterdir() if p.is_dir() and not p.is_symlink() and p.name.startswith("p24-"))
lake=project/".lake"
if lake.is_dir():
    roots += sorted(p for p in lake.iterdir() if p.is_dir() and not p.is_symlink() and p.name.startswith("p24-"))
skip={"native-cache","lib",".git","node_modules","audit","owned"}
files=[]
root_summaries=[]
issues=[]
seen=set()
for top in roots:
    total=0
    total_bytes=0
    selected_count=0
    for directory,dirs,names in os.walk(top,followlinks=False):
        pdir=Path(directory)
        depth=len(pdir.relative_to(top).parts)
        dirs[:]=sorted(d for d in dirs if d not in skip and not (pdir/d).is_symlink() and depth<5)
        for name in sorted(names):
            p=pdir/name
            try:
                st=p.lstat()
            except OSError as e:
                issues.append({"path":str(p),"error":str(e)}); continue
            if not stat.S_ISREG(st.st_mode):
                continue
            total+=1; total_bytes+=st.st_size
            lower=name.lower()
            archive=lower.endswith((".tar.gz",".tar.xz",".tgz"))
            metadata=(lower.endswith(".json") and (any(k in lower for k in ("registry","record","snapshot","manifest","source-map")) or st.st_size>=1048576))
            if not (archive or metadata) or st.st_size<1048576:
                continue
            s=str(p)
            if s in seen: continue
            seen.add(s); selected_count+=1
            files.append({"path":s,"bytes":st.st_size,"allocated_bytes":st.st_blocks*512,
                          "links":st.st_nlink,"inode":st.st_ino,"device":st.st_dev,
                          "mtime_ns":st.st_mtime_ns,
                          "category":"compressed-derived-archive" if archive else "diagnostic-metadata-candidate",
                          "under_canonical_worktree":p.is_relative_to(project),
                          "protected_baseline":top.name.startswith("p24-baseline")})
    root_summaries.append({"root":str(top),"read_depth_limit":5,"regular_files_stat":total,
                           "regular_bytes_stat":total_bytes,"selected_large_files":selected_count})
files.sort(key=lambda r:(-r["bytes"],r["path"]))
hashed_bytes=0
hash_budget=2*1024**3
for item in files:
    if hashed_bytes+item["bytes"]>hash_budget:
        item["sha256_not_computed"]="read-only probe hash budget"; continue
    p=Path(item["path"])
    before=p.stat()
    h=hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda:f.read(1048576),b""): h.update(chunk)
    after=p.stat()
    item["sha256"]=h.hexdigest()
    item["unchanged_while_reading"]=(before.st_size,before.st_mtime_ns,before.st_ino)==(after.st_size,after.st_mtime_ns,after.st_ino)
    hashed_bytes+=item["bytes"]
groups={}
for x in files:
    if "sha256" in x: groups.setdefault(x["sha256"],[]).append(x)
duplicates=[{"sha256":sha,"bytes_each":xs[0]["bytes"],"paths":[x["path"] for x in xs]} for sha,xs in groups.items() if len(xs)>1]
v=os.statvfs(ws)
try:
    pin=subprocess.check_output(["git","rev-parse","HEAD"],cwd=project,text=True).strip()
except Exception as e:
    pin=str(e)
print(json.dumps({"kind":"P24_READ_ONLY_STORAGE_INVENTORY","source_pin":pin,
                 "workspace_free_bytes":v.f_bavail*v.f_frsize,"workspace_available_blocks":v.f_bavail,
                 "block_bytes":v.f_frsize,"scope":"p24 diagnostic roots and canonical .lake/p24 roots, depth<=5; no native/lib/audit/owned traversal",
                 "file_count":len(files),"hashed_bytes":hashed_bytes,"mutations_performed":False,
                 "note":"Candidates only; no deletion permission or originality classification is inferred from name.",
                 "elapsed_seconds":round(time.monotonic()-started,3)},sort_keys=True))
for x in root_summaries:
    if x["selected_large_files"]: print("ROOT "+json.dumps(x,sort_keys=True))
for x in files: print("FILE "+json.dumps(x,sort_keys=True))
for x in duplicates: print("DUPLICATE "+json.dumps(x,sort_keys=True))
for x in issues: print("ISSUE "+json.dumps(x,sort_keys=True))
P24_READ_ONLY_STORAGE_INVENTORY
