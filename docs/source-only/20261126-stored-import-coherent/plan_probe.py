"""Generate an import-only plan, never invoke Lean or publish CI."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import re
from verify_package_parts import read_lock, verify

PARENT="ImbalancedChen.P5SubdivisionStoredParentTypes"
BLOCKS=tuple(f"ImbalancedChen.Data.P5SubdivisionStoredBlock{i:03}" for i in range(72))
H_AGG="ed93ab0ca2a1b6e3f537c5349baa60f13d94b9cae26abd161364e67b5d4d07c0"
H_LAKE="35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849"
H_TRANSPORT="6fdee2329166c014d14657df5098cd92aa5f1592305268bd4ef9be82e48915ee"
POLICY_FLAGS=["-t0","-j2","-M12288","-D","warningAsError=true"]

def need(ok, reason):
    if not ok:
        raise ValueError(reason)

def sha(value):
    return hashlib.sha256(value).hexdigest()

def physical(path):
    path=path.absolute()
    need(path.resolve(strict=True)==path, "not a physical path: "+str(path))
    return path

def read_pinned(path, expected):
    data=physical(path).read_bytes()
    need(sha(data)==expected,"pinned bytes mismatch: "+str(path))
    return data

def import_header(raw):
    lines=raw.decode().splitlines()
    imports=re.findall(r"(?m)^import ([A-Za-z0-9_.]+)$",raw.decode())
    need(tuple(imports)==BLOCKS and lines[:72]==["import "+n for n in BLOCKS], "frozen aggregate imports changed")
    return ("import "+PARENT+"\n"+"\n".join(lines[:72])+"\n").encode()

def unique(roots, relative, expected):
    actual=[]
    for root in roots:
        p=root/relative
        if p.exists() or p.is_symlink():
            need(p.is_file() and p.resolve(strict=True)==p.absolute(),"shadow or nonphysical module candidate: "+str(p))
            actual.append(p.absolute())
    need(actual==[expected.absolute()],"module import unavailable or shadowed: "+relative)

def compose(project, overlay, core, aggregate, pkg_lock):
    project,overlay,core=map(physical,(project,overlay,core))
    need(all(p.is_dir() for p in (project,overlay,core)), "required root not a directory")
    need(not overlay.is_relative_to(project) and not project.is_relative_to(overlay), "overlay and stock roots must be disjoint")
    lake=json.loads(read_pinned(project/"lake-manifest.json",H_LAKE))
    receipt=json.loads(read_pinned(overlay/"TRANSPORT_RECEIPT.json",H_TRANSPORT))
    modules=receipt["modules"]
    names=(PARENT,*BLOCKS)
    need(receipt["status"]=="VERIFIED_PAIRS_MATERIALIZED_NOT_IMPORTED" and set(modules)==set(names),"incorrect transport receipt")
    lock=read_lock(pkg_lock)
    p=verify(project,lock)
    need(p["status"]=="PASS_PACKAGE_BYTES_ONLY",f"warm package files incomplete: {p['verified']}/665")
    ids={PurePosixPath(path).parts[2] for path in lock}
    selected=[p["name"] for p in lake["packages"] if p["name"] in ids]
    need(len(selected)==len(ids) and set(selected)==ids, "pinned package inventory changed")
    libs=[physical(project/".lake/packages"/n/".lake/build/lib/lean") for n in selected]
    roots=[physical(overlay/"lib"),*libs]
    need(len(set(roots+[core]))==len(roots)+1, "duplicate import root")
    for root in roots:
        for coreName in ("Lean","Init","Std"):
            need(not (root/coreName).exists() and not list(root.glob(coreName+".*")), "library shadows sysroot: "+str(root/coreName))
    inputs={}
    for n in names:
        stem=n.replace(".","/")
        src=overlay/"source"/(stem+".lean")
        obj=roots[0]/(stem+".olean")
        unique(roots+[core],stem+".olean",obj)
        for suffix in (".olean.private",".olean.server",".ir",".ir.sig"):
            need(not any((r/(stem+suffix)).exists() or (r/(stem+suffix)).is_symlink() for r in roots+[core]),"unexpected extra facet: "+stem+suffix)
        read_pinned(src,modules[n]["source_sha256"])
        read_pinned(obj,modules[n]["olean_sha256"])
        inputs[n]=[str(src),str(obj),modules[n]["source_sha256"],modules[n]["olean_sha256"]]
    # The original restored parent remains solely for stock qualification; it is
    # intentionally excluded from LEAN_PATH, so only one parent can be selected.
    stock_parent=project/".lake/build/lib/lean"/(PARENT.replace(".","/")+".olean")
    read_pinned(stock_parent,modules[PARENT]["olean_sha256"])
    for path in lock:
        if path.endswith(".olean"):
            rel=path.split("/.lake/build/lib/lean/",1)[1]
            unique(roots+[core],rel,project/path)
    probe=import_header(read_pinned(aggregate,H_AGG))
    return probe, {
        "status":"PHYSICAL_INPUT_PLAN_ONLY_NOT_IMPORTED",
        "protected_modules":inputs,
        "stock_parent_retained_but_not_in_search_path":str(stock_parent),
        "lean_path":os.pathsep.join(map(str,roots)),
        "official_core_root_expected_in_dist":str(core),
        "argv_prefix":POLICY_FLAGS,
        "probe_sha256":sha(probe),
        "package_count":len(lock),
        "stdlib_origin_must_also_be_verified_by_existing_runtime_guard":True,
        "lean_invoked":False,
        "proof_accepted":False,
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ("project","overlay","core","aggregate","package-lock","emit"):
        p.add_argument("--"+name,type=Path,required=True)
    a=p.parse_args()
    probe,plan=compose(a.project,a.overlay,a.core,a.aggregate,a.package_lock)
    installed=a.project/"StoredImportProbe.lean"
    need(read_pinned(installed,plan["probe_sha256"])==probe, "installed probe differs")
    a.emit.mkdir(mode=0o700)
    plan["exact_guard_arguments"]=POLICY_FLAGS+[str(physical(installed))]
    (a.emit/"PLAN.json").write_text(json.dumps(plan,indent=2,sort_keys=True)+"\n")
    print(plan["status"],len(plan["protected_modules"]),plan["package_count"])

if __name__=="__main__":
    main()
