#!/usr/bin/env python3
"""Read-only Part 2 round-four preflight; NOT a Lean/kernel receipt.

A separately pinned old round-three checkout runs its unchanged acceptance
checker in CI. This script additionally binds the inherited twelve module
bytes, the frozen seven-field witness, the new sixty-four row stream and
the exact generated certificate inputs. It does not claim real-integral proof.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
DATA = ROOT / "verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json"
OLD = ROOT / "verification/part2/round3/batch4-to64/receipt.json"
SOURCE_SHA256 = "f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7"
SOURCE_BLOB = "49499697cca96de5f7b779e95077874ce5f9d119"
OLD_RECEIPT_BLOB = "fc1b4061f4b6dfbd9e5ac8476cdfd4eac431e516"
EXPECTED_OLD_STATUS = "PASS_STRICT_TRUST0_STOCK_REPLAY_OWNED_AUDIT"
STREAM_64_128 = "30338bd676b26db92eb58aeea28455eed63350f0003afabc143d583c451b61cb"
STREAM_0_128 = "8b2b8ab5ddc4db399044bd8c874eb0b8e4274503366031db6640a4f70dbfa2fa"
COLUMNS = [
    "group", "t_index", "u_index", "exact_Z",
    "discarded_floor_Q80", "extra_lower_Q160", "extra_upper_Q160"
]
BATCH_LO, BATCH_HI = 203655144233934, 203655262611628
PREFIX_LO, PREFIX_HI = 406911671777567, 406911907846016
SCALE = 10**20


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def sha_and_blob(data: bytes) -> tuple[str, str]:
    return (
        hashlib.sha256(data).hexdigest(),
        hashlib.sha1(b"blob " + str(len(data)).encode() + b"\x00" + data).hexdigest(),
    )


def unique_pairs(pairs):
    out = {}
    for name, value in pairs:
        require(name not in out, "Repeated JSON key " + name)
        out[name] = value
    return out


def main() -> None:
    raw = DATA.read_bytes()
    require(sha_and_blob(raw) == (SOURCE_SHA256, SOURCE_BLOB),
            "Frozen source bytes changed")
    require(b"\r\n" in raw, "Original source CRLF lost")
    source = json.loads(raw, object_pairs_hook=unique_pairs)
    require(source["row_columns"] == COLUMNS, "Source column order changed")
    require(source["omega_argument_threshold"] == "7/3", "Buchstab threshold changed")
    require(source["omega_lower"] == "11/20", "Omega lower constant changed")
    require(Fraction(source["K"]) == Fraction(8452171,1250000), "K changed")
    rows = source["rows"]
    require(len(rows) == 17572, "Source row count changed")
    require(all(len(row) == 7 for row in rows[:128]), "Missing raw source fields")
    require(all(row[0] == "E0" and int(row[4]) == 0 for row in rows[:128]),
            "Wrong E0/floor source range")
    require(all(type(row[1]) is int and type(row[2]) is int
                for row in rows[:128]), "Indices not exact integers")
    stream = lambda begin,end: "".join(",".join(map(str, row)) + "\n"
                                        for row in rows[begin:end]).encode()
    require(hashlib.sha256(stream(64,128)).hexdigest() == STREAM_64_128,
            "New row stream changed")
    require(hashlib.sha256(stream(0,128)).hexdigest() == STREAM_0_128,
            "Cumulative LF row stream changed")
    require(stream(0,64) + stream(64,128) == stream(0,128),
            "Concatenation changed")
    keys = [512 * row[1] + row[2] for row in rows[:128]]
    require(all(0 <= row[1] < 512 and 0 <= row[2] < 512 for row in rows[:128]),
            "Grid out of range")
    require(all(a < b for a,b in zip(keys, keys[1:])),
            "Grid cell not strictly increasing across whole prefix")

    old_raw = OLD.read_bytes()
    require(sha_and_blob(old_raw)[1] == OLD_RECEIPT_BLOB,
            "Frozen round-three receipt bytes changed")
    receipt = json.loads(old_raw, object_pairs_hook=unique_pairs)
    require(receipt["status"] == EXPECTED_OLD_STATUS, "Historic status changed")
    require(receipt["proof_common_baseline"] ==
            "1a80c1bcce67886f699d097fc37fd245cd3620bf", "Baseline changed")
    require(receipt["manuscript_commit"] ==
            "ba6ec11d800eccc54406490631895e174de85766",
            "Frozen manuscript changed")
    inventory = receipt["new_modules"] + receipt["reused_modules"]
    require(len(inventory) == 12, "Historical twelve-module count changed")
    require(len({mod["module"] for mod in inventory}) == 12, "Duplicate old module")
    for module in inventory:
        path = ROOT / module["source"]
        require(sha_and_blob(path.read_bytes())[0] ==
                module["source_identity"]["sha256"],
                "Historical source changed: " + module["module"])

    generator = ROOT / "verification/part2/generate_paired_prefix.py"
    result = subprocess.run([
        sys.executable, str(generator), str(DATA),
        "--start", "64", "--count", "64",
        "--check-generated", str(ROOT / "ImbalancedChen/Certificates"),
    ], cwd=ROOT, text=True, capture_output=True)
    require(result.returncode == 0,
            "Exact new generator check failed:\n" + result.stdout + result.stderr)
    report = json.loads(result.stdout, object_pairs_hook=unique_pairs)
    require(report["row_stream_sha256"] == STREAM_64_128, "Report stream changed")
    require(report["original_ordinals"] == list(range(64, 128)),
            "Original ordinals were renumbered")
    require(Fraction(report["candidate_lower"]) ==
            Fraction(BATCH_LO,SCALE), "New candidate lower bound changed")
    require(Fraction(report["candidate_upper"]) ==
            Fraction(BATCH_HI,SCALE), "New candidate upper bound changed")
    prefix = (ROOT / "ImbalancedChen/Certificates/PairedV2Prefix128.lean").read_text()
    require("Prefix64.integral + Batch64To128.integral" in prefix,
            "Actual append decomposition missing")
    require(("def lowerBound : ℚ := " + str(PREFIX_LO) + " / " + str(SCALE))
            in prefix, "Cumulative exact lower bound changed")
    require(("def upperBound : ℚ := " + str(PREFIX_HI) + " / " + str(SCALE))
            in prefix, "Cumulative exact upper bound changed")
    require(Fraction(203256527543633 + BATCH_LO, SCALE) ==
            Fraction(PREFIX_LO, SCALE), "Lower addition inconsistent")
    require(Fraction(203256645234388 + BATCH_HI, SCALE) ==
            Fraction(PREFIX_HI, SCALE), "Upper addition inconsistent")
    print(json.dumps({
        "status": "PRECOMPUTATION_AND_INHERITED_BYTES_ONLY",
        "original_ordinals": [64,128], "count": 64,
        "cumulative_prefix": [0,128],
        "row_stream_sha256": STREAM_64_128,
        "prefix_stream_sha256": STREAM_0_128,
        "inherited_receipt_blob": OLD_RECEIPT_BLOB,
        "inherited_module_count": len(inventory),
        "candidate_interval_numerators": [BATCH_LO, BATCH_HI],
        "cumulative_interval_numerators": [PREFIX_LO, PREFIX_HI],
        "denominator": SCALE,
        "requires": "strict trust0 compilation + original leanchecker + owned-declaration audit",
    }, indent=2))


if __name__ == "__main__":
    main()
