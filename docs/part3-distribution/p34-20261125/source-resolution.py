"""Inspect the two pinned trees without importing or compiling Lean code."""
import base64
import collections
import functools
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
import zipfile

BASE = "fa22a56829ee880404516a36d498ce27dcb32f92"
P3 = "ef1479c272bdd6b24800fa10409d793f0a2fe95c"
Y04 = "docs/source-only/20261123-yellow-node-owners/Y04_SPECTRAL_SOURCE_SELECTION.json"
PREVIOUS = "b5c82eb80a1b20235b5be9463165171667ae71b83b58cd93df29c1e48bceee9b"
T8 = "docs/source-only/20261110-yellow-closure-10t/t08_actual_spectral_supplier/"
T4 = "docs/source-only/20261112-resume/t04/"
T25 = "docs/source-only/20261112-resume/t25-fixed-kloosterman-tail/"
T22 = "docs/source-only/20261122-resume/ten-task-continuation/ImbalancedChen/"
T30 = "docs/source-only/20261102-resume-30r/"
TARGETS = {
    "child-1": [(T30+"actual_spectral_energy/Part3OriginalSignedNativeCuspFourier", "original_negative_row_native_conjugate original_negative_row_native_norm"),
                (T30+"oldform_continuous/Part3OriginalPrincipalTraceRow", "original_principal_trace_row_removal original_principal_trace_row_norm_sq")],
    "source-d7c20fd154": [(T8+"Part3OriginalExceptionalJNativeCompletion","original_chart_J_completion"),
                          (T8+"Part3OriginalHolomorphicCuspFrames","original_positive_holomorphic_product"),
                          (T8+"Part3OriginalPositiveMaassCentralTransform","original_central_row")],
    "source-02f097a275": [(T8+"Part3ActualYoungCriticalCusps","all_cusps_critical"),
                          (T8+"Part3ActualCriticalCuspEvaluation","ae_native_cusps_independent"),
                          (T8+"Part3OriginalCharacterTraceRow","actual_character_row_squared")],
    "source-ac61270cfe": [(T4+"spectral-next/Part3ActualZeroModeSpatialGram","native_horizontal_edges_vanish spatial_gram"),
                          (T8+"Part3OriginalCuspidalPoincareTrace",""), (T8+"Part3OriginalContinuousPoincarePackets","")],
    "source-c11432a253": [(T4+"projection-next/Part3ActualContinuousResolution","nativeSynthesis_analysis_eq_projection"),
                          (T4+"projection-next/Part3OriginalProjectedContinuousCovariance","original_projected_trace"),
                          (T4+"mixed-continuous-next/Part3OriginalMarkedWeakAdjoint","original_marked_weak")],
    "source-5d163eba78": [(T8+"Part3ActualEisensteinReciprocalGrowth","relative_reciprocal_bound"),
                          (T8+"Part3ActualEisensteinOrdinaryGrowth","original_ordinary_factors")],
    "source-12218e6031": [(T8+"Part3ActualCriticalScatteringUnitarity","actual_critical_scattering_unitary"),
                          (T22+"Part3CriticalConstantPairTail","criticalPair_tailL2_iff criticalPair_zero_tailL2_iff ordinaryInfinityMean_tailL2_iff"),
                          (T22+"Part3NativeCriticalMeanTail","nativeMean_tailL2_iff")],
    "source-be795bf299": [(T8+"Part3ActualResidualVolumeNormalization","native_residue_inverse_volume"),
                          (T8+"Part3OriginalResidualPoincarePackets","original_residual_packets")],
    "source-b838bef941": [(T25+"Part3FixedMarkEulerSummability","physical_twisted_summable"),
                          (T25+"Part3OriginalCrossCuspWeightTwoTail","original_weight_two_absolute")],
    "source-4f9bf9d0fc": [(T4+"positive-full-six-next/Part3OriginalBothSignsSixSpectrum","original_six_spectrum")],
}
# Previously observed results allow mismatches to be disclosed after regenerating.
PRIOR_COUNTS = [(250,23,14,0),(648,50,25,22),(318,27,15,0),(736,49,28,28),
                (756,49,29,28),(323,27,15,0),(391,29,15,2),(716,48,28,23),
                (136,0,8,0),(1070,59,41,29)]
OUT = Path(__file__).resolve().parent / "source-resolution-recovery.json"
os.chdir(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
batch = subprocess.Popen(["git","cat-file","--batch"],stdin=subprocess.PIPE,stdout=subprocess.PIPE)

def blob(oid):
    batch.stdin.write((oid+"\n").encode())
    batch.stdin.flush()
    header = batch.stdout.readline().split()
    data = batch.stdout.read(int(header[-1]))
    assert batch.stdout.read(1)==b"\n"
    return data

def tree_at(commit):
    rows = subprocess.check_output(["git","ls-tree","-rz",commit]).decode().split("\0")
    return {p:m.split()[2] for line in rows if line for m,p in [line.split("\t",1)]}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def module_name(path):
    name = path.replace("\\","/").rsplit("/",1)[-1].removesuffix(".txt")
    name = re.sub(r"__[a-f0-9]{64}(?=\.lean$)","",name).replace(".reused.lean",".lean")
    name = name.removeprefix("ImbalancedChen.")
    return "ImbalancedChen."+name[:-5] if re.fullmatch(r"\w+\.lean", name) else None

def record_module(s):
    if not isinstance(s,str):
        return None
    if re.fullmatch(r"ImbalancedChen(?:\.\w+)+",s):
        return s
    return module_name(s)

def registry_hashes(j, reg, index, parent=None):
    if isinstance(j,list):
        for child in j:
            registry_hashes(child,reg,index)
    if not isinstance(j,dict):
        return
    name_keys = ("path","file","source","source_path","module","name","intended_module",
                 "module_name","canonical_path","relative_path","repo_path")
    install_keys = ("intended_install_relative_path","required_install_path","intended_install_path",
                    "install_path","intended_module","module_name")
    names = {record_module(j.get(k)) for k in name_keys} | {record_module(parent)}
    installed = {record_module(j.get(k)) for k in install_keys}
    if isinstance(j.get("module"),str):
        match = re.fullmatch(r"(?:transitive )?(ImbalancedChen(?:\.\w+)+)",j["module"])
        if match:
            installed.add(match[1])
    names.discard(None)
    installed.discard(None)
    if len(installed)==1:
        names=installed
    if len(names)==1:
        n=next(iter(names))
        for k in ("sha256","source_sha256","raw_sha256","content_sha256","file_sha256"):
            h=j.get(k)
            if isinstance(h,str) and re.fullmatch("[a-f0-9]{64}",h):
                index[n][h].add(reg)
    for k,v in j.items():
        n=record_module(k)
        values=v if isinstance(v,list) else [v]
        if n and all(isinstance(h,str) and re.fullmatch("[a-f0-9]{64}",h) for h in values):
            for h in values:
                index[n][h].add(reg)
        if isinstance(v,(list,dict)):
            registry_hashes(v,reg,index,k)

def decoded_members(path,data):
    if path.endswith(".b64"):
        yield from decoded_members(path[:-4],base64.b64decode(data))
    elif path.endswith((".tar",".tar.xz",".tar.gz",".tgz")):
        with tarfile.open(fileobj=io.BytesIO(data),mode="r:*") as tar:
            for entry in tar:
                if entry.isfile():
                    yield "tar",path+"!"+entry.name,tar.extractfile(entry).read()
    elif path.endswith(".zip"):
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for entry in z.infolist():
                if not entry.is_dir():
                    yield "zip",path+"!"+entry.filename,z.read(entry)
    elif path.endswith(".gz"):
        yield "gzip",path+"!gunzip",gzip.decompress(data)

class Index:
    def __init__(self, commit, read_registries=False):
        self.tree=tree_at(commit)
        self.candidates=collections.defaultdict(dict)
        self.hash_paths=collections.defaultdict(list)
        self.registry=collections.defaultdict(lambda:collections.defaultdict(set))
        self.data={}
        self.oid={}
        self.counts=collections.Counter()
        hashed_sources=collections.defaultdict(list)
        groups=collections.defaultdict(list)
        for p,oid in self.tree.items():
            groups[oid].append(p)
        self.counts.update(tracked_paths=len(self.tree),distinct_git_blobs=len(groups))
        for oid, paths in groups.items():
            data=blob(oid)
            h=sha(data)
            self.hash_paths[h].extend(paths)
            for p in paths:
                n=module_name(p) if p.endswith((".lean",".lean.txt")) else None
                if n:
                    kind="lean" if p.endswith(".lean") else "attachment"
                    self.candidates[n][p]=(h,kind)
                    self.oid[h]=oid
                elif p.endswith(".json") and read_registries and (b".lean" in data or b"ImbalancedChen." in data):
                    try:
                        registry_hashes(json.loads(data),p,self.registry)
                    except (ValueError,RecursionError):
                        pass
                elif p.endswith(".raw") and b"import " in data[:6000]:
                    hashed_sources[h].append(p)
                    self.oid[h]=oid
            for typ,p,b in decoded_members(paths[0],data):
                self.counts[typ+"_members"]+=1
                g=sha(b)
                self.hash_paths[g].append(p)
                n=module_name(p) if p.endswith((".lean",".lean.txt")) else None
                if n:
                    self.candidates[n][p]=(g,"archive_member")
                    self.data[g]=b
                if typ=="gzip" and b"import " in b[:6000]:
                    hashed_sources[g].append(p)
                    self.data[g]=b
        for n,hashes in self.registry.items():
            for h in hashes:
                for p in hashed_sources.get(h,[]):
                    self.candidates[n].setdefault(p,(h,"hash_matched_payload"))

    def bytes_of(self,h):
        return self.data[h] if h in self.data else blob(self.oid[h])

@functools.lru_cache(None)
def imports(h):
    text=base.bytes_of(h).decode("utf8","replace")
    # Only the header can contain Lean imports. Preserve line breaks and remove nested
    # block comments, line comments and quoted literal contents before reading it.
    tokens=re.finditer(r'/-|-/|--|"|\\.|\n|[^/"\\\n-]+|.',text)
    depth=0
    string=line=False
    cleaned=[]
    for token in tokens:
        s=token[0]
        if s=="\n":
            cleaned.append(s)
            line=False
        elif line:
            continue
        elif depth:
            depth+=int(s=="/-")-int(s=="-/")
        elif string:
            if s=='"':
                string=False
        elif s=="/-":
            cleaned.append(" ")
            depth=1
        elif s=="--":
            line=True
        elif s=='"':
            cleaned.append(" ")
            string=True
        else:
            cleaned.append(s)
    lines=re.findall(r"(?m)^[ \t]*(?:(?:public|private|meta|all)\s+)*import\s+([^\n]+)","".join(cleaned))
    return sorted({n for line in lines for n in re.findall(r"(?:^|\s)(ImbalancedChen(?:\.\w+)+)\b",line)})

base=Index(BASE,True)
other=Index(P3)
prefer={n:r["sha256"] for n,r in json.loads(blob(base.tree[Y04]))["available_sources"].items()}
def choose(n):
    return min(base.candidates[n],key=lambda p:(
        p!=n.replace(".","/")+".lean",base.candidates[n][p][0]!=prefer.get(n),
        ("lean","attachment","archive_member","hash_matched_payload").index(base.candidates[n][p][1]),
        len(p),p))

def walk(entry):
    start=module_name(entry)
    seen={}
    absent=set()
    stack=[start]
    while stack:
        n=stack.pop()
        if n in seen or n in absent:
            continue
        if not base.candidates[n]:
            absent.add(n)
            continue
        p=entry if n==start else choose(n)
        seen[n]=p
        stack.extend(imports(base.candidates[n][p][0]))
    return set(seen),absent

def stats(names,absent):
    variants=sorted(n for n in names if len({h for h,_ in base.candidates[n].values()})>1)
    archived=sorted(n for n in names if not any(k=="lean" for _,k in base.candidates[n].values()))
    return dict(counts=[len(names),len(absent),len(variants),len(archived)],missing=sorted(absent),
                different_sha256_names=variants,only_attachment_or_archive=archived)

leaves={}
catalog={}
union=set()
all_absent=set()
for (leaf,items),before in zip(TARGETS.items(),PRIOR_COUNTS):
    names=set()
    absent=set()
    terminals=[]
    for f,symbols in items:
        p=f+".lean"
        h=sha(blob(base.tree[p]))
        declarations=re.findall(r"^\s*(?:theorem|lemma)\s+([\w']+)",blob(base.tree[p]).decode(),re.M)
        names_in_file=symbols.split() or declarations[-1:]
        assert set(names_in_file)<=set(declarations)
        reach,miss=walk(p)
        names.update(reach)
        absent.update(miss)
        reg_paths=base.registry[module_name(p)].get(h,set())
        preferred=sorted(q for q in reg_paths if PurePosixPath(q).parent in (PurePosixPath(p).parent,PurePosixPath(p).parent.parent))
        terminals.append(dict(path=p,sha256=h,terminal_names=names_in_file,neighboring_registries=preferred,
                              resolved_modules=sorted(reach),**stats(reach,miss)))
    info=stats(names,absent)
    leaves["P3.4."+leaf]=dict(terminals=terminals,observed_prior_counts=before,
        matches_prior_counts=info["counts"]==list(before),**info)
    union.update(names)
    all_absent.update(absent)
for n in sorted(union):
    selected=choose(n)
    catalog[n]={"default_path":selected,"imports_of_default":imports(base.candidates[n][selected][0]),
                "candidates":[dict(path=p,sha256=h,kind=k) for p,(h,k) in sorted(base.candidates[n].items())]}
def lookup(tree,n,hashes):
    return dict(name_candidates={p:h for p,(h,k) in sorted(tree.candidates[n].items())},
                matching_digest_paths={h:sorted(tree.hash_paths[h]) for h in sorted(hashes) if h in tree.hash_paths})
child=leaves["P3.4.child-1"]["missing"]
unresolved={}
for n in sorted(all_absent):
    hashes=base.registry[n]
    unresolved[n]=dict(registered_sha256={h:sorted(paths) for h,paths in sorted(hashes.items())},
                       baseline_lookup=lookup(base,n,hashes),remote_tip_lookup=lookup(other,n,hashes))
child_remote={n:unresolved[n]["remote_tip_lookup"] for n in child}
report=dict(
    baseline=BASE,comparison_branch="codex/p3-continuation-20261124",comparison_commit=P3,
    prior_report={"status":"Original scratch JSON and the two temporary generators were lost on remount. This is a new report recomputed from Git objects.",
                  "previously_observed_sha256":PREVIOUS,"old_sha256_applies_to_this_file":False},
    method={"columns":["distinct resolved module names, including targets","unresolved module names","names with multiple distinct source digests","names with only attachment or archive bytes"],
            "scope":"Representative terminal source paths are pinned independently per board row. Follow explicit ImbalancedChen imports only. Ignore Mathlib and other upstream packages; alternative candidate combinations are not traversed. Counts are unions per leaf.",
            "selection":"Pin each terminal to its registered source-only path. For its dependencies prefer the production path ImbalancedChen/<module>.lean, then the source hash in Y04, then tracked Lean, tracked .lean.txt, named archive member or digest-matched opaque source payload. Shorter path then lexical order break ties. Retain different digest candidates even when a preferred version is available.",
            "source_checks":"Use git ls-tree -rz and git cat-file --batch at the two commits. Search .lean/.lean.txt and ZIP/tar sources, including .reused and __<sha256> member names; recognize base64 archives. Attach registry-linked, exact-checksummed .raw or decoded gzip sources. For missing sources compare registered hashes against all raw Git blobs and all decoded archive members irrespective of filename.",
            "prior_missing_name_check":"The lost report also checked missing names in tracked JSON, Markdown, text, TSV, SHA lists, JSONL, patches and diffs. This reconstruction records hash registries and source-byte lookups, without reproducing that ancillary text-reference index.",
            "limitations":"A dependency selected by this static rule may be incompatible with its callers. A digest match establishes byte identity only. Neither compilation, kernel replay nor axiom checks are part of this audit. The remote lookup covers the pinned tree and its archive bytes, not prior revisions."},
    tree_scans={BASE:dict(base.counts),P3:dict(other.counts)},leaf_count=len(leaves),terminal_count=sum(map(len,TARGETS.values())),
    all_prior_leaf_counts_reproduced=all(x["matches_prior_counts"] for x in leaves.values()),
    total_unresolved=len(all_absent),total_unresolved_with_registered_hash=sum(bool(base.registry[n]) for n in all_absent),
    child_1_remote=dict(searched=len(child),source_names_found=sum(bool(z["name_candidates"]) for z in child_remote.values()),
                        modules_with_digest_match=sum(bool(z["matching_digest_paths"]) for z in child_remote.values()),lookups=child_remote),
    leaves=leaves,unresolved_modules=unresolved,resolved_module_catalog=catalog)
OUT.write_text(json.dumps(report,ensure_ascii=False,indent=1)+"\n")
batch.stdin.close()
batch.wait()
print(OUT,sha(OUT.read_bytes()))
print("counts",[(k,v["counts"]) for k,v in leaves.items()])
print("prior_counts_match",report["all_prior_leaf_counts_reproduced"],"missing",len(all_absent),"with_hash",report["total_unresolved_with_registered_hash"],"remote_child_hit",report["child_1_remote"]["source_names_found"],report["child_1_remote"]["modules_with_digest_match"])
