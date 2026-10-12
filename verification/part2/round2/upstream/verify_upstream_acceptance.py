#!/usr/bin/env python3
"""Verify this archived P0 receipt's byte/type/object bindings; do not invoke Lean.

Run from any working directory. The accepted historical compile/replay gates
are reused only when the receiving source files and locked inputs match.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo-root", type=Path, default=here.parents[3])
    args = ap.parse_args()
    repo = args.repo_root.resolve()
    manifest = json.loads((here / "UPSTREAM_ACCEPTANCE.json").read_text())
    require(manifest["acceptance_mode"] == "EXACT_SOURCE_UPSTREAM_REUSE", "Unexpected acceptance mode")
    require(manifest["compiled_or_kernel_replayed_in_this_receiving_round"] is False,
            "This script cannot attest a new Lean compile or replay")
    raw_objects = {}
    for obj in manifest["original_archive_files"]:
        raw = (here / obj["path"]).read_bytes()
        require(len(raw) == obj["bytes"], f"Size mismatch: {obj['path']}")
        require(sha256(raw) == obj["sha256"], f"SHA256 mismatch: {obj['path']}")
        require(git_blob(raw) == obj["git_blob_sha1"], f"Git blob mismatch: {obj['path']}")
        raw_objects[obj["upstream_path"]] = raw
    for obj in manifest["repository_required_objects"] + manifest["modules"]:
        raw = (repo / obj["path"]).read_bytes()
        expected_sha = obj.get("accepted_source_sha256", obj.get("sha256"))
        expected_blob = obj.get("accepted_git_blob_sha1", obj.get("git_blob_sha1"))
        require(sha256(raw) == expected_sha, f"Receiver source/input mismatch: {obj['path']}")
        require(git_blob(raw) == expected_blob, f"Receiver Git blob mismatch: {obj['path']}")
        raw_objects[obj["path"]] = raw
    ledger = manifest["ledger_selection"]
    ledger_raw = (here / ledger["path"]).read_bytes()
    require(sha256(ledger_raw) == ledger["sha256"], "Ledger selection hash mismatch")
    ledger_rows = {m["module"]: m for m in json.loads(ledger_raw)["modules"]}
    allowed = {"Classical.choice", "Quot.sound", "propext"}
    modules = {m["module"]: m for m in manifest["modules"]}
    total = 0
    for batch in manifest["batches"]:
        base = here / batch["batch"]
        receipt = json.loads((base / "receipt.json").read_text())
        guard = json.loads((base / "source-guard.json").read_text())
        types = json.loads((base / "compiler-types.json").read_text())
        counts = json.loads((base / "axiom-counts.json").read_text())
        require(receipt["all_scoped_gates"] == "passed", "Upstream gates did not pass")
        require(receipt["toolchain"] == manifest["toolchain"], "Toolchain mismatch")
        require(guard["exit_code"] == 0, "Source guard did not pass")
        require(len(types) == receipt["declaration_count"] == batch["declaration_count"], "Count mismatch")
        require(len({t["name"] for t in types}) == len(types), "Repeated declaration")
        count_map = collections.Counter(t["module"] for t in types)
        require(count_map == {c["module"]: c["count"] for c in counts}, "Module inventory mismatch")
        for t in types:
            require(set(t["axioms"]) <= allowed and t["kind"] != "axiom", f"Forbidden axiom: {t['name']}")
            require("⋯" not in t["type"] and "⋯" not in t["readable_type"], f"Truncated type: {t['name']}")
        audit = receipt["modules"][0]["gates"]["owned_axiom_audit"]
        audit_lines = raw_objects[audit["retained_log"]].decode().splitlines()
        audited_types = [json.loads(x.removeprefix("P0_AUDIT_DECL "))
                         for x in audit_lines if x.startswith("P0_AUDIT_DECL ")]
        audited_counts = [json.loads(x.removeprefix("P0_AUDIT_MODULE "))
                          for x in audit_lines if x.startswith("P0_AUDIT_MODULE ")]
        require(audited_types == types and audited_counts == counts, "Audit log/type records mismatch")
        require(f"P0_AUDIT_COUNT {len(types)}" in audit_lines, "Audit completion marker missing")
        for path, expected in receipt["files_sha256"].items():
            if path in raw_objects:
                require(sha256(raw_objects[path]) == expected, f"Receipt object mismatch: {path}")
        for m in receipt["modules"]:
            accepted = modules[m["module"]]
            require(m["current_source_sha256"] == accepted["accepted_source_sha256"], "Accepted source mismatch")
            require(m["current_git_blob"] == accepted["accepted_git_blob_sha1"], "Accepted blob mismatch")
            require(m["owned_declaration_count"] == accepted["owned_declaration_count"] == count_map[m["module"]],
                    "Owned declaration count mismatch")
            record = next(x for x in guard["records"] if x["module"] == m["module"])
            require(record["sha256"] == m["current_source_sha256"] and record["source_guard"] == "passed",
                    "Source guard binding mismatch")
            l = ledger_rows[m["module"]]
            require(l["current_source"]["source_sha256"] == m["current_source_sha256"], "Ledger source mismatch")
            require(l["integration_acceptance"]["accepted"] and not l["outstanding_validation_gates"],
                    "Ledger acceptance mismatch")
            for name, gate in m["gates"].items():
                require(gate["returncode"] == 0 and gate["metadata_adapter"] is False, f"Gate failed: {name}")
                require(gate["source_sha256_before"] == gate["source_sha256_after"], "Source changed during gate")
                require(gate.get("import_olean_sha256_before") == gate.get("import_olean_sha256_after"),
                        "Imports changed during gate")
                if "verification_passed" in gate:
                    require(gate["verification_passed"] and not gate["verification_failure_reasons"], "Gate binding failed")
                lines = raw_objects[gate["retained_log"]].decode().splitlines()
                require(all(k in gate and gate[k] == v for k, v in json.loads(lines[0]).items()),
                        "Log preamble/receipt mismatch")
                if name != "owned_axiom_audit":
                    require(gate["source_sha256_before"] == m["current_source_sha256"] and
                            gate["olean_sha256"] == m["olean_sha256"], "Production object binding mismatch")
                if name == "stock_kernel_replay":
                    require(Path(gate["command"][0]).name == "leanchecker" and
                            gate["command"][1:] == ["--verbose", m["module"]], "Unexpected replay command")
                    require(gate["target_olean_sha256_before"] == m["olean_sha256"], "Replayed object mismatch")
                    require(f"replaying {m['module']}" in lines, "Missing replay log")
                else:
                    require(gate["trustLevel"] == 0 and gate["strict"] is True, "Compile was not strict/trust-zero")
                    require(f"FRONTEND_OK module={gate['module']} trustLevel=0" in lines, "Compile completion missing")
        total += len(types)
    require(len(modules) == 6 and total == 253, "Expected six production modules and 253 declarations")
    print(json.dumps({"status": "PASS_EXACT_SOURCE_UPSTREAM_REUSE", "modules": len(modules),
                      "declarations": total, "original_archive_files": len(manifest["original_archive_files"]),
                      "new_lean_compile_or_replay": False,
                      "proof_source_commit": manifest["proof_source_commit"],
                      "evidence_source_commit": manifest["evidence_source_commit"]}, indent=2))


if __name__ == "__main__":
    main()
