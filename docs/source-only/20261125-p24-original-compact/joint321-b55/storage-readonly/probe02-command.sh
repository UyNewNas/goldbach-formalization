set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
python3 -B - <<'P24_FILESYSTEM_AND_DIAGNOSTIC_READ_ONLY'
from pathlib import Path
import hashlib,json,os,stat,subprocess,time,shutil
started=time.monotonic()
ws=Path("/workspace"); canonical=ws/"p2-4-compact-proof-20261125"
mounts=[]
for line in Path("/proc/self/mountinfo").read_text().splitlines():
    left,right=line.split(" - ",1); lf=left.split(); rf=right.split()
    mp=lf[4]
    if mp=="/" or mp=="/workspace" or str(ws).startswith(mp.rstrip("/")+"/"):
        opts=rf[2].split(",")
        mounts.append({"mount_point":mp,"mount_options":lf[5],"filesystem_type":rf[0],"source":rf[1],
                       "super_options":opts,"mount_info_fields":lf[:6]})
print("FILESYSTEM "+json.dumps({"mounts":mounts,"statfs":subprocess.check_output(["stat","-f","-c","%T %t %S %b %f %a",str(ws)],text=True).strip(),
              "readonly_tools_available":{x:shutil.which(x) for x in ["findmnt","btrfs","xfs_info","zfs","filefrag","compsize"]},
              "capability_tests_performed":False,"write_mount_dedupe_compression_performed":False},sort_keys=True))
protected={"native-cache","native","lib","audit","owned",".git","node_modules","packages","build","logs"}
large=[]; total_summaries=[]; issues=[]
def inspect(top,canonical_only=False):
    selected=0; files=0; logical=0; allocated=0; excluded=[]
    for directory,dirs,names in os.walk(top,followlinks=False):
        d=Path(directory); rel=d.relative_to(top); depth=len(rel.parts)
        kept=[]
        for n in sorted(dirs):
            p=d/n
            block = n in protected or p.is_symlink() or depth>=5
            if n==".lake" and p!=canonical/".lake": block=True
            if str(p).startswith(str(canonical/"ImbalancedChen")): block=True
            if p==canonical/"verification" or p==canonical/"docs" or p==canonical/"diagnostics": block=True
            if n.startswith("p24-baseline"): block=True
            if block: excluded.append(str(p))
            else: kept.append(n)
        dirs[:]=kept
        for n in names:
            p=d/n
            try: s=p.lstat()
            except OSError as e: issues.append({"path":str(p),"error":str(e)});continue
            if not stat.S_ISREG(s.st_mode):continue
            files+=1;logical+=s.st_size;allocated+=s.st_blocks*512
            if p==canonical/".lake/p2-private/records.json":continue
            text=p.suffix.lower() in {".json",".txt",".md",".yaml",".yml"}
            archive=n.lower().endswith((".tar.gz",".tar.xz",".tgz"))
            if s.st_size>=1048576 and (text or archive):
                large.append({"path":str(p),"bytes":s.st_size,"allocated_bytes":s.st_blocks*512,"links":s.st_nlink,
                              "device":s.st_dev,"inode":s.st_ino,"mtime_ns":s.st_mtime_ns,
                              "category":"archive" if archive else "ordinary-metadata-text",
                              "under_canonical_worktree":p.is_relative_to(canonical)})
                selected+=1
    return {"root":str(top),"inspected_regular_files":files,"inspected_logical_bytes":logical,
            "inspected_allocated_bytes":allocated,"maximum_depth":5,
            "totals_exclude_protected_and_deeper_subtrees":True,"excluded_subtree_count":len(excluded),
            "excluded_subtrees":excluded[:25],"large_metadata_or_archive_count":selected}
for p in sorted(ws.iterdir()):
    s=p.lstat()
    if stat.S_ISDIR(s.st_mode):
        if p.name in {"p2-private-20261124","mathlib","goldbach-p2"} or p.name.startswith(("native","lean","mathlib")):
            total_summaries.append({"root":str(p),"not_traversed":"known native/environment/baseline root","directory_inode_bytes_only":s.st_blocks*512})
        else:
            total_summaries.append(inspect(p))
    elif stat.S_ISREG(s.st_mode):
        if s.st_size>=1048576:
            large.append({"path":str(p),"bytes":s.st_size,"allocated_bytes":s.st_blocks*512,"links":s.st_nlink,
                          "device":s.st_dev,"inode":s.st_ino,"mtime_ns":s.st_mtime_ns,"category":"workspace-top-file",
                          "under_canonical_worktree":False})
budget=2*1024**3; used=0
for item in sorted(large,key=lambda x:x["path"]):
    if item["bytes"]+used>budget:
        item["sha256_not_computed"]="2GiB read budget";continue
    p=Path(item["path"]);a=p.stat();h=hashlib.sha256()
    with p.open("rb") as f:
        for c in iter(lambda:f.read(1048576),b""):h.update(c)
    b=p.stat();used+=item["bytes"];item["sha256"]=h.hexdigest()
    item["unchanged_while_reading"]=(a.st_size,a.st_mtime_ns,a.st_ino)==(b.st_size,b.st_mtime_ns,b.st_ino)
for x in total_summaries:print("ROOT "+json.dumps(x,sort_keys=True))
for x in sorted(large,key=lambda x:-x["bytes"]):print("FILE "+json.dumps(x,sort_keys=True))
for x in issues:print("ISSUE "+json.dumps(x,sort_keys=True))
v=os.statvfs(ws)
print("SUMMARY "+json.dumps({"mutations_performed":False,"source_pin":subprocess.check_output(["git","rev-parse","HEAD"],cwd=canonical,text=True).strip(),
              "free_bytes":v.f_bavail*v.f_frsize,"large_file_count":len(large),"hashed_bytes":used,
              "elapsed_seconds":round(time.monotonic()-started,3),
              "scope_note":"Bounded stat totals exclude native/source/object/audit/log/baseline subtrees; not du totals of protected content."},sort_keys=True))
P24_FILESYSTEM_AND_DIAGNOSTIC_READ_ONLY
