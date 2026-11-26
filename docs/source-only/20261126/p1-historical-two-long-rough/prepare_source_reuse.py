#!/usr/bin/env python3
"""Reproduce only this packet's original-byte source layering. No Lean calls."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BASE = "f3084a33ca08daf305ddd7c6eb660a038794614a"
PREFIX = "docs/source-only/20261126/p1-historical-two-long-rough/"

def sha(b):
    return hashlib.sha256(b).hexdigest()

def blob(b):
    return hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()

def pin(path, b):
    return {"path": path, "bytes": len(b), "sha256": sha(b), "git_blob": blob(b)}

def origin(path):
    b = (REPO / path).read_bytes()
    old = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=REPO)
    assert b == old, "Original archive changed: " + path
    return b

def save(rel, b):
    p = HERE / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(b)
    return pin(PREFIX + rel, b)

def cut(path, first, stop, namespace, owner):
    b = origin(path)
    a = b.index(first.encode())
    z = b.index(stop.encode(), a)
    block = b[a:z]
    names = re.findall(rb"^(?:private )?(?:def|theorem|lemma|abbrev) ([^\s(:]+)", block, re.M)
    return {"source": pin(path, b), "base_commit": BASE,
            "namespace": namespace, "owner": owner,
            "source_byte_range": [a,z], "source_line_range": [b[:a].count(b"\n")+1,b[:z].count(b"\n")],
            "block_sha256": sha(block), "block_bytes": len(block),
            "declarations": [namespace + "." + n.decode() for n in names]}, block

sub_path = "docs/source-only/20261102-resume-30k/twolong_source/Part3TwoLongLiteralBrunSubstitution.lean"
e1_dir = "docs/source-only/20261121-resume/p4-actual-coprime-E1/ImbalancedChen/"
e3_dir = "docs/source-only/20261121-resume/p4-pair-rough-E3/ImbalancedChen/"
S = "ImbalancedChen.P1HistoricalTwoLongBrunSubstitutionData"
M = "ImbalancedChen.P1HistoricalTwoLongExactPairMeanData"
R = "ImbalancedChen.P1HistoricalTwoLongFiniteRoughData"
specs = [
    (sub_path, "def divisorIndicator", "variable {ι", "ImbalancedChen.Part3.TwoLongLiteralBrunSubstitution", S),
    (e1_dir+"P4BOriginalSameRhoCoprimeE1.lean", "def pairMean ", "def pairMain ", "ImbalancedChen.P4BOriginalSameRhoCoprimeE1", M),
    (e3_dir+"P4BOriginalPairMeanNorm.lean", "def densityLog ", "/-- The three moment orders", "ImbalancedChen.P4BOriginalPairMeanNorm", M),
    (e3_dir+"P4BOriginalTwiceMeanPayment.lean", "def gapPairMean ", "def twiceMeanSum ", "ImbalancedChen.P4BOriginalTwiceMeanPayment", R),
    (e3_dir+"P4BOriginalRoughPairFinite.lean", "def polyR ", "end\nend ImbalancedChen.P4BOriginalRoughPairFinite", "ImbalancedChen.P4BOriginalRoughPairFinite", R),
    (e3_dir+"P4BOriginalEnvelopePolynomialPayment.lean", "def p2Price ", "/-- Strong absolute-q sum", "ImbalancedChen.P4BOriginalEnvelopePolynomialPayment", R),
]
blocks = [cut(*s) for s in specs]
notice = "/-! SOURCE ONLY / UNCOMPILED. Original declaration bytes are preserved;\nsee EXTRACTION_BINDING.json. No compilation or kernel credit is added. -/\n"

def section(ns, opens, data):
    return ("namespace "+ns+"\nnoncomputable section\n"+opens+"\n").encode()+data+("end\nend "+ns+"\n").encode()

sub = ("import ImbalancedChen.Part3TwoLongBrunSupport\n"
       "import ImbalancedChen.Part3TwoLongHBMellinBrunProfiles\n"
       "import ImbalancedChen.PrimeProductsMellinExactMeanInsertion\n\n"+notice).encode()
sub += section(blocks[0][0]["namespace"],
    "open Classical Set\nopen scoped BigOperators\n"
    "open TwoLongActualLowerBrunMoment TwoLongHBMellinBrunProfiles\n"
    "open TwoLongLiteralMellinModes TwoLongFixedMRectangularCore\n"
    "open ImbalancedChen.OriginalOneLongLiteralBrunDictionary\n"
    "open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b (smallPrimes)\n"
    "open ImbalancedChen.PrimeProducts\n", blocks[0][1])

mean = ("import ImbalancedChen.P4BOriginalBrunCoprimeE1\n"
        "import ImbalancedChen.TotientReciprocalBudget\n\n"+notice).encode()
mean += section(blocks[1][0]["namespace"],
    "open Classical Set\nopen scoped BigOperators SchwartzMap\n"
    "open P4BOriginalBrunCoprimeE1\n"
    "open Part3.TwoLongLiteralMellinModes (wideWindow)\n"
    "open Part3.TwoLongLiteralBrunSubstitution (brunPolynomial)\n",blocks[1][1])
mean += b"\n" + section(blocks[2][0]["namespace"],
    "open Classical Set\nopen scoped BigOperators SchwartzMap\n"
    "open P4BOriginalCoprimeSmoothE1 (mass price price_nonneg)\n"
    "open P4BOriginalBrunCoprimeE1\n"
    "open Part3.TwoLongActualLowerBrunMoment (brunSupport brunSupport_bounds)\n",blocks[2][1])

rough = ("import "+M+"\nimport ImbalancedChen.P4BOriginalPositiveLongEnvelope\n"
         "import ImbalancedChen.P5ActualHBRoughBrunFinite\n"
         "import ImbalancedChen.Part3TwoLongBrunComplexGap\n"
         "import ImbalancedChen.P4BOriginalSquarefreeP2\n\n"+notice).encode()
for i in [3,4,5]:
    source = origin(specs[i][0])
    ns = blocks[i][0]["namespace"]
    start = source.index(("namespace "+ns).encode())
    end = blocks[i][0]["source_byte_range"][0]
    header = source[start:end]
    header = b"\n".join(line for line in header.split(b"\n")
        if not line.startswith(b"open P4BOriginalTwoLongExpandedCore")
        and not line.startswith(b"open P4BOriginalFiniteSmoothCount"))
    rough += header + blocks[i][1] + ("end\nend "+ns+"\n\n").encode()

owners = {
    S: save("support/P1HistoricalTwoLongBrunSubstitutionData.lean",sub),
    M: save("support/P1HistoricalTwoLongExactPairMeanData.lean",mean),
    R: save("support/P1HistoricalTwoLongFiniteRoughData.lean",rough),
}
for m,p in owners.items():
    p["module"] = m
    p["literal_imports"] = re.findall(r"^import ([^\s]+)",(REPO/p["path"]).read_text(),re.M)

rows=[]
for row, block in blocks:
    ob = (REPO/owners[row["owner"]]["path"]).read_bytes()
    a = ob.index(block)
    assert ob.count(block) == 1
    row["owner_path"] = owners[row["owner"]]["path"]
    row["owner_byte_range"] = [a,a+len(block)]
    row["owner_line_range"] = [ob[:a].count(b"\n")+1,ob[:a+len(block)].count(b"\n")]
    source=origin(row["source"]["path"])
    sa,sz=row["source_byte_range"]
    import_end = max(x.end() for x in re.finditer(rb"^import [^\n]+\n",source,re.M))
    insertion=("import "+row["owner"]+"\n").encode()
    post=source[:import_end]+insertion+source[import_end:sa]+source[sz:]
    pr=save("postimages/"+Path(row["source"]["path"]).name,post)
    pr["original_coordinate_edits"]=[
        {"range":[import_end,import_end],"insert_utf8":insertion.decode()},
        {"range":[sa,sz],"delete_sha256":sha(block)}]
    pr["all_other_original_bytes_unchanged"]=True
    pr["status"]="FUTURE_PROVIDER_POSTIMAGE_UNCOMPILED_NOT_ACTIVE_IMPORT"
    row["complementary_postimage"]=pr
    rows.append(row)

routes=[]
for filename,old,new in [
    ("P4BOriginalCoprimeSmoothE1.lean","import ImbalancedChen.Part3TwoLongLiteralBrunSubstitution\n","import "+S+"\n"),
    ("P4BOriginalPositiveLongEnvelope.lean","import ImbalancedChen.P4BOriginalPairMeanNorm\n","import ImbalancedChen.P4BOriginalBrunCoprimeE1\n")]:
    path=(e1_dir if "Coprime" in filename else e3_dir)+filename
    b=origin(path)
    assert b.count(old.encode())==1
    post=b.replace(old.encode(),new.encode())
    p=save("selected-api/"+filename,post)
    routes.append({"source":pin(path,b),"source_commit":BASE,"selected":p,
      "old_import_utf8":old,"new_import_utf8":new,
      "all_declaration_and_proof_bytes_unchanged":True,
      "module":"ImbalancedChen."+Path(filename).stem})

manifest={"schema":"p15_historical_two_long_rough_exact_source_layering_v1",
 "status":"SOURCE_ONLY_UNCOMPILED_ZERO_FORMAL_CREDIT", "source_anchor":BASE,
 "shared_brun_support":{"module":"ImbalancedChen.Part3TwoLongBrunSupport",
    "path":"docs/source-only/20261126/p1-historical-two-long-p2/support/Part3TwoLongBrunSupport.lean",
    "sha256":"65fdf24bbb25ec01b5bee87ef30127dcad1230a6f28b1ff6cb802d46e7d98f38",
    "second_owner_created":False},
 "owners":list(owners.values()),"extractions":rows,"import_routing_only":routes,
 "preserved_namespaces":True,"preserved_declaration_bytes":True,
 "old_provider_selection":"If any old provider is later compiled alongside these new owners, select its complementary postimage. Archived originals remain immutable and are not a second active owner.",
 "acceptance":{"compiled":False,"kernel_verified":False,"full_owned_audit":False,"P1_5_complete":False}}
(HERE/"EXTRACTION_BINDING.json").write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({"status":"SOURCE_LAYERING_WRITTEN", "owners":len(owners),"blocks":len(rows),
 "original_declarations":sum(len(x["declarations"]) for x in rows),"import_only_routes":len(routes),
 "manifest_sha256":sha((HERE/"EXTRACTION_BINDING.json").read_bytes())}))
