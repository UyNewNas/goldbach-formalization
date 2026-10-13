#!/usr/bin/env python3
"""Round 5 E0 [128,192) exact-data preflight, NOT Lean/kernel certification."""
from __future__ import annotations
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
DATA = ROOT / "verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json"
NEW_DATA = ROOT / "ImbalancedChen/Certificates/PairedV2Batch128To192Data.lean"
PREFIX = ROOT / "ImbalancedChen/Certificates/PairedV2Prefix192.lean"
DATA_SHA = "f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7"
DATA_BLOB = "91a43426ac475bed88182ab1a39c3f4997902b12"
STREAM_SHA = "2afc4ad5661676de82d4a9af6a101ad2e0f487ae46c98a155710fcda122e811e"
PREFIX_SHA = "b32c7adb0daff5b9de4da559d4597ff805ed7bd644268b348795fcd52959a8fa"
DEN = 10 ** 20

def check(cond, reason):
    if not cond:
        raise AssertionError(reason)

def gitblob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()

def main():
    raw = DATA.read_bytes()
    check(hashlib.sha256(raw).hexdigest() == DATA_SHA and b"\r\n" in raw,
          "Frozen source bytes or CRLF format changed")
    src = json.loads(raw)
    check(len(src["rows"]) == 17572, "Total source count changed")
    check(src["row_columns"] == [
        "group","t_index","u_index","exact_Z","discarded_floor_Q80",
        "extra_lower_Q160","extra_upper_Q160"], "Raw field order changed")
    check(Fraction(src["K"]) == Fraction(8452171, 1250000), "Frozen K changed")
    check(src["omega_argument_threshold"] == "7/3", "Omega threshold changed")
    rows = src["rows"][:192]
    check(all(len(r)==7 and r[0]=="E0" and int(r[4]) == 0 for r in rows),
          "E0/witness fields changed")
    pairs = [(r[1],r[2]) for r in rows]
    check(all(isinstance(a,int) and isinstance(b,int) and 0 <= a < 512 and 0 <= b < 512
              for a,b in pairs), "Not a valid integer grid index")
    keys = [a*512+b for a,b in pairs]
    check(all(a < b for a,b in zip(keys,keys[1:])), "Grid index overlap or reordering")
    stream = lambda lo,hi: "".join(",".join(map(str,r))+"\n" for r in src["rows"][lo:hi]).encode()
    check(hashlib.sha256(stream(128,192)).hexdigest()==STREAM_SHA, "New LF row stream changed")
    check(hashlib.sha256(stream(0,192)).hexdigest()==PREFIX_SHA, "Prefix LF stream changed")
    check(stream(0,128)+stream(128,192)==stream(0,192), "Nonconcatenated source rows")
    check(gitblob(NEW_DATA.read_bytes())==DATA_BLOB, "Generated candidate Lean data bytes changed")
    proof = PREFIX.read_text()
    check("Prefix128.integral + Batch128To192.integral" in proof
          and "Fin.sum_univ_add (a := 128) (b := 64)" in proof,
          "Cumulative finite integral append missing")
    check("Fin.castAdd 64 i" in proof and "Fin.natAdd 128 i" in proof,
          "Malformed Fin 192 = Fin 128 + Fin 64 indices")
    check(("def lowerBound : ℚ := 610834375909440 / "+str(DEN)) in proof,
          "Cumulative lower bound source mismatch")
    check(("def upperBound : ℚ := 610834730821178 / "+str(DEN)) in proof,
          "Cumulative upper bound source mismatch")
    cmd = [sys.executable,
           str(ROOT/"verification/part2/generate_paired_prefix.py"),
           str(DATA), "--start","128","--count","64","--check-generated",
           str(ROOT/"ImbalancedChen/Certificates")]
    ran = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    check(ran.returncode==0, "Generator check failed:\n"+ran.stdout+ran.stderr)
    report = json.loads(ran.stdout)
    check(report["row_stream_sha256"]==STREAM_SHA and
          report["original_ordinals"]==list(range(128,192)), "Generator ordinals or stream changed")
    check(Fraction(report["candidate_lower"]) == Fraction(203922704131873,DEN)
          and Fraction(report["candidate_upper"]) == Fraction(203922822975162,DEN),
          "New exact candidate certificate bounds changed")
    check(Fraction(406911671777567+203922704131873,DEN)==
          Fraction(610834375909440,DEN), "Lower append sum mismatch")
    check(Fraction(406911907846016+203922822975162,DEN)==
          Fraction(610834730821178,DEN), "Upper append sum mismatch")
    print(json.dumps({
        "status":"PRECOMPUTATION_ONLY_NOT_LEAN", "source_sha256":DATA_SHA,
        "row_stream_sha256":STREAM_SHA,"prefix_stream_sha256":PREFIX_SHA,
        "new_rows":[128,192],"cumulative_rows":[0,192],
        "distinct_grid_cells":192,
        "new_bounds_numerators":[203922704131873,203922822975162],
        "prefix_bounds_numerators":[610834375909440,610834730821178],
        "denominator":DEN,
        "requires":"strict Lean trustLevel=0, stock leanchecker, all-declaration and transitive axiom audit"
    },indent=2))

if __name__ == "__main__":
    main()
