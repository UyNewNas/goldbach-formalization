#!/usr/bin/env python3
"""Verify the archived, source-bound Part 2 prefix acceptance without running Lean.

This is a receiving check of actual execution evidence, not an integral prover.
The integral proofs are the Lean sources and their recorded stock-kernel replays.
Run check.sh to obtain new Lean executions on a normally supported toolchain.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
sys.path.insert(0, str(ROOT))
from verification.verify_variable_envelope_boxes import lean_code


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def identity(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
            "git_blob_sha1": hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()}


def read(path):
    return json.loads(path.read_text())


def gate(entry, action):
    item = entry[action]
    receipt = read(BASE / item["receipt"])
    lines = (BASE / item["log"]).read_text().splitlines()
    require(receipt["action"] == action and receipt["module"] == entry["module"],
            "Gate action/module mismatch")
    require(receipt["returncode"] == 0 and receipt["verification_passed"] is True
            and receipt["failures"] == [], "Unsuccessful execution receipt")
    require(receipt["metadata_adapter"] is False, "Unexpected metadata adapter")
    require(receipt["environment"]["LEAN_NUM_THREADS"] == "1", "Thread setting changed")
    require(receipt["object_sha256_after"] == entry["object_sha256"], "Output object mismatch")
    require(Path(receipt["log"]).name == Path(item["log"]).name, "Wrong raw log")
    preamble = json.loads(lines[0])
    for key, value in preamble.items():
        require(receipt[key] == value, "Log/receipt preamble mismatch: " + key)
    for key in ["source_sha256", "shared_sha256", "local_producer_sha256"]:
        require(receipt[key + "_before"] == receipt[key + "_after"],
                "Changed gate input: " + key)
    if action == "compile":
        require(receipt["trustLevel"] == 0 and receipt["warningAsError"] is True,
                "Missing strict trust-zero compilation")
        require(receipt["source"].endswith("/" + entry["source"]), "Wrong compiled source")
        require(receipt["source_sha256_after"] == entry["source_identity"]["sha256"],
                "Compiled source mismatch")
        require("FRONTEND_OK module=" + entry["module"] + " trustLevel=0" in lines,
                "Missing successful stock frontend marker")
        require(Path(receipt["command"][0]).name == "lake"
                and receipt["command"][-1] == "strict", "Unexpected compile command")
    else:
        require(receipt["object_sha256_before"] == receipt["object_sha256_after"],
                "Replayed object changed")
        require(receipt["command"][-2:] == ["--verbose", entry["module"]]
                and Path(receipt["command"][0]).name == "leanchecker",
                "Unexpected stock kernel replay command")
        require("replaying " + entry["module"] in lines, "Missing selected-module kernel replay")
    return receipt


def main():
    report = read(BASE / "receipt.json")
    require(report["status"] == "PASS_STRICT_TRUST0_STOCK_REPLAY_OWNED_AUDIT",
            "Acceptance is not complete")
    for relative, expected in report["source_inputs"].items():
        require(identity(ROOT / relative) == expected, "Source identity changed: " + relative)
    for relative, expected in report["archive_files"].items():
        require(identity(BASE / relative) == expected, "Archived evidence changed: " + relative)
    modules = report["all_production_modules"]
    actual_sources = {str(p.with_suffix("").relative_to(ROOT)).replace("/", ".")
                      for p in (ROOT / "ImbalancedChen/Certificates").rglob("*.lean")}
    require(set(modules) == actual_sources and len(modules) == 9,
            "Production source inventory differs")
    for module in modules:
        source = ROOT / (module.replace(".", "/") + ".lean")
        require(not re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b",
                              lean_code(source.read_text())), "Forbidden proof escape: " + module)
    expected_objects = {}
    for entry in report["new_modules"]:
        gate(entry, "compile")
        gate(entry, "replay")
        expected_objects[entry["module"]] = entry["object_sha256"]
    require(len(expected_objects) == 3, "Wrong new-module coverage")
    upstream = read(ROOT / report["upstream_acceptance"])
    require(upstream["production_module_count"] == 6, "Wrong upstream coverage")
    for entry in upstream["modules"]:
        expected_objects[entry["module"]] = entry["olean_sha256"]
    audit = report["audit"]
    audit_gate = gate(audit, "compile")
    local_objects = audit_gate["local_producer_sha256_before"]
    for module, expected in expected_objects.items():
        suffix = "/" + module.replace(".", "/") + ".olean"
        found = [value for path, value in local_objects.items() if path.endswith(suffix)]
        require(found == [expected], "Audit imported another producer: " + module)
    audit_lines = (BASE / audit["compile"]["log"]).read_text().splitlines()
    records = [json.loads(line.removeprefix("P2_AUDIT_DECL "))
               for line in audit_lines if line.startswith("P2_AUDIT_DECL ")]
    counts = [json.loads(line.removeprefix("P2_AUDIT_MODULE "))
              for line in audit_lines if line.startswith("P2_AUDIT_MODULE ")]
    totals = [int(line.removeprefix("P2_AUDIT_COUNT "))
              for line in audit_lines if line.startswith("P2_AUDIT_COUNT ")]
    require(records == read(BASE / "compiler-types.json"), "Compiler type records changed")
    require(totals == [len(records)] == [309], "Declaration census mismatch")
    require(len({r["name"] for r in records}) == len(records), "Duplicate declaration")
    require(counts == audit["module_counts"], "Module census mismatch")
    require(set(expected_objects) == set(modules) == {c["module"] for c in counts},
            "Incomplete module audit")
    counter = Counter(r["module"] for r in records)
    for item in counts:
        require(counter[item["module"]] == item["count"] > 0, "Wrong module count")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for record in records:
        require(record["kind"] != "axiom" and set(record["axioms"]) <= allowed,
                "Forbidden axiom dependency")
        for field in ["type", "readable_type"]:
            require(isinstance(record[field], str) and record[field]
                    and "⋯" not in record[field], "Missing or truncated compiler type")
    for batch in ["p2-first", "p2-coarse"]:
        old_records = read(ROOT / "verification/part2/round2/upstream" / batch / "compiler-types.json")
        current = {r["name"]: r for r in records}
        require(all(current[r["name"]] == r for r in old_records),
                "Reused declarations differ from accepted compiler types")
    generated = read(BASE / "generated-report.json")
    require(generated["count"] == 4 and generated["original_ordinals"] == [0, 1, 2, 3]
            and generated["group"] == "E0", "Wrong actual source slice")
    for filename, expected in generated["generated_sha256"].items():
        require(identity(ROOT / "ImbalancedChen/Certificates" / filename)["sha256"] == expected,
                "Generated source hash mismatch")
    print(json.dumps({"status": "PASS_ARCHIVED_PREFIX4_ACCEPTANCE", "new_modules": 3,
                      "reused_modules": 6, "all_owned_declarations": 309,
                      "new_owned_declarations": 56, "actual_rows": [0, 1, 2, 3],
                      "new_lean_compile_or_replay_in_this_receiving_check": False}, indent=2))


if __name__ == "__main__":
    main()
