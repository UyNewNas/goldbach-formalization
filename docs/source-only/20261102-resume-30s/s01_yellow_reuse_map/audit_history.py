import json, hashlib, pathlib, re, os, subprocess
root=pathlib.Path(r"E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation")
d=root/"docs/source-only/20261102-resume-30s/s01_yellow_reuse_map"
m=json.loads((d/"MAP.json").read_text(encoding="utf-8"))
targets={}
for group in m["source_groups"]:
    for s in group["sources"]:
        mod=s.get("module"); sha=s.get("sha256"); path=s.get("path")
        if not mod and path and str(path).endswith(".lean"):
            mod="ImbalancedChen."+pathlib.Path(path).stem
        if mod and sha: targets.setdefault(mod,set()).add(sha)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
pins={"lean-toolchain":sha(root/"lean-toolchain"),"lakefile.toml":sha(root/"lakefile.toml"),"lake-manifest.json":sha(root/"lake-manifest.json")}
result=subprocess.run(["rg","--files","--hidden","--no-ignore","verification/proof-continuation/2026-10-15/compilation","verification/proof-continuation/2026-10-15/unaccepted-attempts","-g","receipt.json"],cwd=root,capture_output=True,text=True,check=False)
files={root/p.strip() for p in result.stdout.splitlines() if p.strip()}
matches=[]; same_module=[]
for p in sorted(files):
    try: x=json.loads(p.read_text(encoding="utf-8-sig"))
    except Exception: continue
    if not isinstance(x,dict): continue
    status=x.get("status"); module=x.get("module") or x.get("intended_module")
    b=x.get("binding",{}) if isinstance(x.get("binding",{}),dict) else {}
    source_hash=b.get("source_sha256") or x.get("source_sha256")
    direct=b.get("direct_source_sha256",{}) if isinstance(b.get("direct_source_sha256",{}),dict) else {}
    source_path=x.get("source_path") or b.get("source_path")
    exact=[]
    if module in targets and source_hash in targets[module]: exact.append({"module":module,"sha256":source_hash,"kind":"module_source"})
    for dm,dh in direct.items():
        if dm in targets and dh in targets[dm]: exact.append({"module":dm,"sha256":dh,"kind":"direct_source"})
    if source_path:
        for tm, hashes in targets.items():
            if pathlib.Path(str(source_path)).stem==tm.split(".")[-1] and source_hash in hashes:
                exact.append({"module":tm,"sha256":source_hash,"kind":"source_path"})
    if exact:
        bp=b.get("pins",{}) if isinstance(b.get("pins",{}),dict) else x.get("pin_files_sha256",{})
        pin_eq={k:(bp.get(k)==v) for k,v in pins.items() if k in bp}
        matches.append({"receipt_path":str(p.relative_to(root)),"status":status,"module":module,"exact_source_matches":exact,"pins":bp,"current_pin_hashes":pins,"pin_equality":pin_eq,"object_parts":x.get("object_parts"),"exit_code":x.get("exit_code")})
    elif module in targets and status=="PASS":
        same_module.append({"receipt_path":str(p.relative_to(root)),"module":module,"receipt_source_sha256":source_hash,"current_source_sha256s":sorted(targets[module]),"pins":b.get("pins"),"object_parts":x.get("object_parts")})
out={"scope":"read-only local historical proof metadata; no build/compiler/guard/replay","current_pin_hashes":pins,"target_source_module_count":len(targets),"metadata_files_examined":len(files),"exact_same_source_receipts":matches,"same_module_but_source_hash_differs":same_module,"proof_rule":"A prior receipt is reusable only when source byte hash, Lean/toolchain/dependency pin hashes, direct imported source hashes, and required proof evidence all match; module-name match alone is not reuse evidence."}
q=d/"HISTORICAL_EVIDENCE.json"; q.write_text(json.dumps(out,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"source_modules":len(targets),"metadata_files_examined":len(files),"exact_matches":len(matches),"same_module_hash_mismatches":len(same_module),"output":str(q.relative_to(root)),"sha256":sha(q)},ensure_ascii=False))






