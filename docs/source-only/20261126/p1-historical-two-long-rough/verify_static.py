#!/usr/bin/env python3
"""Verify this source-only extraction packet. Never invokes Lean or cloud tools."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]

def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return (REPO/p).read_bytes()
def check_pin(p):
    b=read(p["path"])
    assert len(b)==p["bytes"] and sha(b)==p["sha256"],p["path"]
    return b

def uncomment(text):
    # Nested Lean block comments and line comments. Strings are retained;
    # the selected Lean sources contain no forbidden-word string examples.
    out=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text.startswith("/-",i): depth+=1;i+=2
            elif text.startswith("-/",i): depth-=1;i+=2
            else: i+=1
        elif text.startswith("/-",i): depth=1;i+=2
        elif text.startswith("--",i):
            j=text.find("\n",i);i=len(text) if j<0 else j
        else: out.append(text[i]);i+=1
    assert depth==0,"unclosed block comment"
    return "".join(out)

def verify():
    a=json.loads((HERE/"EXTRACTION_BINDING.json").read_text())
    checks=[]
    for owner in a["owners"]:
        b=check_pin(owner)
        assert re.findall(rb"^import ([^\s]+)",b,re.M)==[s.encode() for s in owner["literal_imports"]]
    checks.append("all_three_shared_owner_hashes_and_literal_imports")
    for row in a["extractions"]:
        src=check_pin(row["source"])
        assert src==subprocess.check_output(["git","show",a["source_anchor"]+":"+row["source"]["path"]],cwd=REPO)
        x,y=row["source_byte_range"];block=src[x:y]
        assert len(block)==row["block_bytes"] and sha(block)==row["block_sha256"]
        dst=read(row["owner_path"]);u,v=row["owner_byte_range"]
        assert dst[u:v]==block
        old=row["complementary_postimage"]
        ins,rem=old["original_coordinate_edits"]
        pos=ins["range"][0];assert ins["range"]==[pos,pos]
        assert rem["range"]==[x,y] and rem["delete_sha256"]==sha(block)
        expected=src[:pos]+ins["insert_utf8"].encode()+src[pos:x]+src[y:]
        assert check_pin(old)==expected
        for name in row["declarations"]:
            short=name.rsplit(".",1)[1].encode()
            pat=rb"^(?:private )?(?:def|theorem|lemma|abbrev) "+re.escape(short)+rb"(?=[\s(:])"
            assert len(re.findall(pat,dst,re.M))==1,(name,"new owner")
            assert not re.search(pat,expected,re.M),(name,"postimage duplicate")
    checks.append("six_original_intervals_byte_identical_to_frozen_git_sources")
    checks.append("all_36_original_declarations_retained_once_in_selected_shared_owner")
    checks.append("all_six_complementary_postimages_exact_insertion_and_deletion")
    for route in a["import_routing_only"]:
        src=check_pin(route["source"])
        assert src==subprocess.check_output(["git","show",a["source_anchor"]+":"+route["source"]["path"]],cwd=REPO)
        old=route["old_import_utf8"].encode();new=route["new_import_utf8"].encode()
        assert src.count(old)==1
        assert check_pin(route["selected"])==src.replace(old,new)
    checks.append("two_selected_generic_providers_change_one_import_only")
    shared=a["shared_brun_support"]
    assert sha(read(shared["path"]))==shared["sha256"]
    assert not list(HERE.rglob("Part3TwoLongBrunSupport.lean"))
    checks.append("original_adjacent_brun_support_hash_and_unique_owner_reuse")
    sources=[]
    for p in sorted(HERE.rglob("*.lean")):
        b=p.read_bytes()
        assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b",uncomment(b.decode())),str(p)
        sources.append({"path":str(p.relative_to(REPO)),"bytes":len(b),"sha256":sha(b)})
    checks.append("all_packet_Lean_sources_free_of_forbidden_proof_tokens")
    # The stop is a precise observed import, not a claim that an absent module
    # does not exist elsewhere or a search of unrelated historical sources.
    modes="docs/source-only/20261028-resume-30/pp_twolong/Part3TwoLongLiteralMellinModes.lean"
    assert sha(read(modes))=="2fce2a53febab40154a9e136882da2c334cbefb65fa662b7369fa7201f750e26"
    assert re.search(rb"^import ImbalancedChen\.Part3TwoLongFixedMRectangularCore\r?$",read(modes),re.M)
    checks.append("observed_fixedM_provider_import_and_importer_fingerprint")
    receipt={"schema":"p15_historical_two_long_rough_static_source_verification_v1",
        "status":"STATIC_EXTRACTION_PASS_SOURCE_ASSEMBLY_BLOCKED",
        "checks":checks,"extracted_original_declarations":sum(len(r["declarations"]) for r in a["extractions"]),
        "packet_Lean_sources":sources,
        "extraction_manifest_sha256":sha((HERE/"EXTRACTION_BINDING.json").read_bytes()),
        "verifier_sha256":sha(Path(__file__).read_bytes()),
        "complete_transitive_source_closure_verified":False,
        "new_historical_rough_terminal_written":False,
        "stop":"Direct fixedMCore provider has no path in current known canonical/source-only file index; see README and SOURCE_REVIEW.",
        "compiled":False,"kernel_verified":False,"full_owned_audit":False,"cloud_jobs":0,
        "formal_credit":0,"P1_5_complete":False}
    (HERE/"STATIC_VERIFICATION.json").write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps({"status":receipt["status"],"checks":len(checks),"original_declarations":receipt["extracted_original_declarations"],
        "receipt_sha256":sha((HERE/"STATIC_VERIFICATION.json").read_bytes())}))

if __name__=="__main__": verify()
