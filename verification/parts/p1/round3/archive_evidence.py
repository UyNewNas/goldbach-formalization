#!/usr/bin/env python3
"""Package existing six-target P1 historical evidence, without running proof gates.

The producer's actual successful receipt is required. Original target commands,
attempt snapshots, checker output, defining-module census and current dependency
bindings are retained. The previous collector's file/hash implementation is
reused; this script neither changes dependencies nor creates verification results.
Compiled objects remain exact hash references and are not embedded in Git.
"""

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tarfile


TARGETS = [
    "ImbalancedChen.HistoricalUpperFiveCellGeometry",
    "ImbalancedChen.ActualHistoricalFifthCellIntegral",
    "ImbalancedChen.ActualHistoricalFifthSavingIntegral",
    "ImbalancedChen.HistoricalFifthCutoffInvariance",
    "verification.parts.p1.round2.HistoricalCellProbe",
    "verification.parts.p1.round3.Part1HistoricalSavingAudit",
]
DEFINING_MODULES = set(TARGETS[:-1])
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PREFIX = "PART1_ROUND3_HISTORY_AUDIT_"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def collect(workspace):
    repo = workspace / "goldbach-formalization"
    runtime = workspace / "lean-runtime"
    current = workspace / "p1-round3-runtime"
    owned = repo / "verification/parts/p1/round3"
    helper = repo / "verification/parts/p1/round2/permit/archive_evidence.py"
    spec = importlib.util.spec_from_file_location("p1_permit_archive_helpers", helper)
    require(spec is not None and spec.loader is not None, "Missing archived collector helpers")
    helpers = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helpers)
    class HistoricalInputs(helpers.Inputs):
        def reference(self, ref, category):
            path = Path(ref['path'])
            if path.name.endswith(('.ir', '.ir.sig', '.ir.hash', '.ir.sig.hash', '.ltar')):
                self.watch(path, ref['sha256'], ref['bytes'])
            else:
                super().reference(ref, category)

    inputs = HistoricalInputs(workspace, repo, runtime)

    receipt_path = current / "part1-round3-final-receipt.json"
    inputs.include(receipt_path, "actual-six-target-final-receipt")
    receipt = json.loads(receipt_path.read_text())
    require(receipt.get("status") == "VERIFIED" and receipt.get("verified") is True,
            "The actual producer gates have not passed")
    require(set(receipt["targets"]) == set(TARGETS), "Unexpected final target scope")
    mode = receipt["verification"]
    require(mode["strict_target_frontends"] == mode["original_checker_calls"] == len(TARGETS)
            and mode["trustLevel"] == 0 and mode["warningAsError"] is True
            and mode["metadata_adapter"] is False
            and mode["official_frontend_api"] == "Lean.Elab.runFrontend"
            and mode["normal_stock_lean_cli_build_executed"] is False
            and mode["fresh_all_import_declaration_replay"] is False
            and mode["original_auxiliary_round2_audit_replayed"] is False,
            "Wrong validation mode or inflated coverage")

    for ref in helpers.refs(receipt):
        inputs.reference(ref, "current-receipt-source-object-or-command-reference")
    require((owned / "VERIFICATION.json").read_bytes() == receipt_path.read_bytes(),
            "The deliverable receipt differs from the actual producer receipt")
    inputs.include(owned / "VERIFICATION.json", "identical-deliverable-receipt")

    for module in TARGETS:
        item = receipt["targets"][module]
        record = item["actual_compile_record"]
        require(record["returncode"] == 0 and record["trustLevel"] == 0
                and record["strict"] is True and record["metadata_adapter"] is False
                and record["compiled_in_round3"] is True
                and record["source_sha256_before"] == record["source_sha256_after"]
                == item["source"]["sha256"] == item["attempt_source_snapshot"]["sha256"]
                and item["original_checker_replayed_defined_declarations"] is True,
                "A target lacks same-source strict compilation and checker evidence: " + module)
        lines = Path(item["raw_compile_log"]["path"]).read_text().splitlines()
        require(lines.count("FRONTEND_OK module=" + module + " trustLevel=0") == 1,
                "Missing actual frontend success: " + module)

    replay = receipt["replay"]["record"]
    require(replay["status"] == "SUCCEEDED" and replay["verified"] is True
            and replay["returncode"] == 0 and replay["expected_targets"] == TARGETS
            and replay["observed_replay_lines"] == TARGETS
            and len(replay["calls"]) == len(TARGETS), "Wrong original-checker coverage")
    checker = receipt["toolchain"]["binaries_rechecked"]["leanchecker"]
    require(replay["commands"] == [[checker["path"], "--verbose", m] for m in TARGETS],
            "Unexpected checker invocation")
    for module, call in zip(TARGETS, replay["calls"]):
        require(call["module"] == module and call["returncode"] == 0
                and call["verified"] is True and call["observed_replay_lines"] == [module],
                "Missing individual checker result: " + module)
        inputs.watch(call["log"], call["log_sha256"])
        inputs.include(call["log"], "original-checker-log")
    inputs.watch(replay["log"], replay["log_sha256"])
    inputs.include(replay["log"], "original-checker-aggregate")

    audit = receipt["audit"]
    lines = Path(audit["raw_log"]["path"]).read_text().splitlines()
    rows = [json.loads(line.removeprefix(PREFIX + "DECL ")) for line in lines
            if line.startswith(PREFIX + "DECL ")]
    counts = dict(Counter(row["module"] for row in rows))
    require(set(counts) == DEFINING_MODULES and counts == audit["module_counts"]
            and len(rows) == len({row["name"] for row in rows}) == audit["declaration_count"]
            and rows == audit["declarations"]
            and set(audit["allowed_axioms"]) == ALLOWED
            and set(audit["observed_axioms"]) <= ALLOWED,
            "Incomplete defining-module declaration census")
    require(lines.count(PREFIX + "COUNT " + str(len(rows))) == 1,
            "Missing complete raw audit count")
    for row in rows:
        require(row["kind"] != "axiom" and set(row["axioms"]) <= ALLOWED and row["type"],
                "Forbidden declaration or missing complete type: " + row["name"])

    closure = receipt["closure"]
    bindings = json.loads(Path(closure["bindings"]["path"]).read_text())
    require(bindings["targets"] == TARGETS
            and bindings["source_module_count"] == closure["source_module_count"]
            and len(bindings["local_modules"]) == closure["local_module_count"]
            and len(bindings["cached_modules"]) == closure["cached_module_count"],
            "Wrong current dependency-binding scope")
    recovered_name = "Batteries.Tactic.OpenPrivate"
    recovered = bindings["cached_modules"][recovered_name]
    require(closure["cached_source_modules_recompiled_in_round3"] == [recovered_name]
            and closure["cached_origin_counts"]["ROUND3_ACTUAL_THIRD_PARTY_SUPPLIER_COMPILATION"] == 1
            and recovered["origin"] == "ROUND3_ACTUAL_THIRD_PARTY_SUPPLIER_COMPILATION"
            and recovered["compiled_in_round3"] is True
            and recovered["source_record"]["metadata_adapter"] is False
            and recovered["source_record"]["returncode"] == 0
            and recovered["historical_cache_label_corrected"] is True,
            "The actual recovered third-party supplier was mislabeled as cache reuse")
    for ref in helpers.refs(bindings):
        inputs.reference(ref, "supplier-source-object-or-original-compilation-log")
    require(sum(len(item['runtime_ir_parts']) for group in ['local_modules', 'cached_modules']
                for item in bindings[group].values()) == closure['current_runtime_ir_file_count'],
            'The current executable IR inventory differs from the receipt')

    # Failed attempts remain failed original records. Nothing in this directory
    # tree is counted as a successful target unless the final receipt binds it.
    inputs.tree(current, "original-round3-attempt-record")
    for diff in sorted((current / "incidents").rglob("*.diff")):
        inputs.include(diff, "reviewed-concurrent-source-diff")
    inputs.tree(workspace / "p1-round3-upstream-intake", "bounded-upstream-read-record")
    inputs.tree(workspace / "p1-round3-final-upstream", "bounded-final-upstream-read-record")
    semantics = replay["semantics"]
    inputs.watch(semantics["source_path"], semantics["source_sha256"])
    inputs.include(semantics["source_path"], "original-checker-semantics")
    inputs.include(helper, "unchanged-reused-archive-helpers")
    for name in ["KEY_THEOREM_TYPES.md", "KEY_THEOREM_TYPES.json", "check.sh", "archive_evidence.py",
                 "verify_archive_parts.py",
                 "PART0_28FD_HISTORY_IMPORT.patch", "PART0_IMPORT_CHECK.json",
                 "PART0_D036_HISTORY_IMPORT.patch", "PART0_D036_IMPORT_CHECK.json",
                 "MATHEMATICAL_AUDIT.md", "BRIDGE_STATIC_REVIEW.md",
                 "INTERFACE_AND_OPEN_INPUTS.md", "RUNTIME_EVENTS.md",
                 "UPSTREAM_INTAKE.md", "upstream-intake.json",
                 "FINAL_P0_INTAKE.md", "FINAL_HEAD_RECHECK.json"]:
        inputs.include(owned / name, "owned-reproduction-or-intake-source")
    inputs.recheck()

    manifest = {
        "kind": "Actual P1 historical fifth saving, same-cap cutoff invariance and integral evidence",
        "receipt_sha256": inputs.watched[receipt_path]["sha256"],
        "verified_targets": TARGETS,
        "target_source_sha256": {m: receipt["targets"][m]["source"]["sha256"] for m in TARGETS},
        "audit_declaration_count": len(rows),
        "audit_module_counts": counts,
        "strict_target_frontends": len(TARGETS),
        "original_checker_calls": len(TARGETS),
        "source_module_count": closure["source_module_count"],
        "local_origin_counts": closure["local_origin_counts"],
        "cached_origin_counts": closure["cached_origin_counts"],
        "cached_source_modules_recompiled_in_round3": closure["cached_source_modules_recompiled_in_round3"],
        "cached_module_count": closure["cached_module_count"],
        "current_runtime_ir_file_count": closure["current_runtime_ir_file_count"],
        "runtime_ir_binding_scope": closure["runtime_ir_binding_scope"],
        "stock_cli_build_executed_here": False,
        "fresh_full_import_declaration_replay": False,
        "original_log_aliases": list(inputs.aliases.values()),
        "members": [{k: v for k, v in item.items() if k != "data"}
                    for item in sorted(inputs.files.values(), key=lambda x: x["member"])],
        "unembedded_verified_references": [
            {"original_path": str(path), **record,
             "reason": "Binary/object or pinned dependency source omitted; exact digest retained"}
            for path, record in sorted(inputs.watched.items()) if path not in inputs.files],
    }
    payloads = {item["member"]: item["data"] for item in inputs.files.values()}
    require(len(payloads) == len(inputs.files), "Duplicate archive member")
    payloads["MANIFEST.json"] = helpers.encoded(manifest)
    output = owned / "EVIDENCE.tar.gz"
    temporary = output.with_name(output.name + ".tmp")
    with temporary.open("wb") as stream:
        with gzip.GzipFile(filename="", mode="wb", fileobj=stream, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w") as archive:
                for name, data in sorted(payloads.items()):
                    entry = tarfile.TarInfo(name)
                    entry.size, entry.mode, entry.mtime = len(data), 0o644, 0
                    archive.addfile(entry, io.BytesIO(data))
    with tarfile.open(temporary, "r:gz") as archive:
        names = archive.getnames()
        require(len(names) == len(set(names)) == len(payloads) and set(names) == set(payloads),
                "Archive inventory mismatch")
        for entry in archive.getmembers():
            require(entry.isfile() and archive.extractfile(entry).read() == payloads[entry.name],
                    "Archive payload mismatch: " + entry.name)
    inputs.recheck()
    temporary.replace(output)
    archive_sha256 = hashlib.sha256(output.read_bytes()).hexdigest()
    archive_bytes = output.stat().st_size
    part_bytes = 8_000_000
    for stale in owned.glob("EVIDENCE.tar.gz.part*"):
        stale.unlink()
    parts = []
    with output.open("rb") as stream:
        index = 0
        while block := stream.read(part_bytes):
            part = owned / f"EVIDENCE.tar.gz.part{index:02d}"
            part.write_bytes(block)
            parts.append({
                "path": part.name,
                "bytes": len(block),
                "sha256": hashlib.sha256(block).hexdigest(),
            })
            index += 1
    combined = hashlib.sha256()
    combined_bytes = 0
    for part in parts:
        data = (owned / part["path"]).read_bytes()
        combined.update(data)
        combined_bytes += len(data)
    require(combined.hexdigest() == archive_sha256 and combined_bytes == archive_bytes,
            "Split archive does not reconstruct the verified tar.gz")
    output.unlink()
    summary = {"status": "ARCHIVED_VERIFIED_HISTORICAL_SAVING_EVIDENCE",
               "archive_filename": output.name, "sha256": archive_sha256,
               "bytes": archive_bytes, "parts": parts, "part_bytes": part_bytes,
               "member_count": len(payloads),
               "payload_bytes": sum(map(len, payloads.values())),
               "receipt_sha256": inputs.watched[receipt_path]["sha256"],
               "verified_reference_count": len(inputs.watched), "binaries_embedded": False,
               "verified_targets": TARGETS,
               "scope": "Six selected targets; no stock build or fresh complete imported-module replay claim"}
    (owned / "ARTIFACT.json").write_bytes(helpers.encoded(summary))
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", required=True, type=Path)
    collect(parser.parse_args().workspace.resolve())
