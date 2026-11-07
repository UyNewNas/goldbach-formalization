#!/usr/bin/env python3
"""Archive existing permit evidence after checking the actual successful receipt.

This is an evidence collector, not a proof checker. It never invokes Lean,
Git, CI or the receipt producer. It preserves original logs and source
snapshots, verifies their hashes, and omits compiled binaries from the archive.
The separately unfinished historical-integral queue is outside its scope.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile


TARGETS = [
    "ImbalancedChen.StoredHistoricalBoxPermit",
    "verification.parts.p1.round2.permit.StoredCapProbe",
    "verification.parts.p1.round2.permit.StoredCapAudit",
]
SOURCES = {
    TARGETS[0]: "50a9dc07e98046a664711572bcf69b58a528c0a97502bbd9f75de245dd43bc0d",
    TARGETS[1]: "41b1ac2242e8b4e84b72c98772bb52b7ec9814807466b9ef19ccb15f4e4dff49",
    TARGETS[2]: "c5cb2cd40e7d8b591302ccb2e3b0e36c2b3a99a786385316feeec62db4617b33",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MODULE_COUNTS = {TARGETS[0]: 14, TARGETS[1]: 22}
TEXT_SUFFIXES = {".json", ".jsonl", ".log", ".txt", ".lean", ".py", ".md", ".toml", ".cpp"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def refs(value):
    if isinstance(value, dict):
        if {"path", "sha256", "bytes"} <= value.keys():
            yield value
        for child in value.values():
            yield from refs(child)
    elif isinstance(value, list):
        for child in value:
            yield from refs(child)


class Inputs:
    def __init__(self, workspace, repo, runtime):
        self.workspace, self.repo, self.runtime = workspace, repo, runtime
        self.watched, self.files, self.aliases = {}, {}, {}

    def watch(self, path, digest=None, size=None):
        path = Path(path).absolute()
        require(path.is_relative_to(self.workspace), f"Input outside workspace: {path}")
        require(path.is_file() and not path.is_symlink(), f"Missing/nonregular input: {path}")
        with path.open("rb") as stream:
            actual = hashlib.file_digest(stream, "sha256").hexdigest()
        length = path.stat().st_size
        require(digest is None or actual == digest, f"Changed input hash: {path}")
        require(size is None or length == size, f"Changed input size: {path}")
        record = {"sha256": actual, "bytes": length}
        require(path not in self.watched or self.watched[path] == record,
                f"Input changed during collection: {path}")
        self.watched[path] = record
        return path, record

    def include(self, path, category):
        path, record = self.watch(path)
        if path in self.files:
            return
        data = path.read_bytes()
        require(hashlib.sha256(data).hexdigest() == record["sha256"], f"Read changed: {path}")
        require(b"\0" not in data, f"Refusing binary archive member: {path}")
        data.decode("utf-8")
        for root, prefix in [(self.repo, "repo"), (self.runtime, "runtime"),
                             (self.workspace, "workspace")]:
            if path.is_relative_to(root):
                member = prefix + "/" + path.relative_to(root).as_posix()
                break
        self.files[path] = {**record, "original_path": str(path), "member": member,
                            "category": category, "data": data}

    def reference(self, ref, category):
        path, _ = self.watch(ref["path"], ref["sha256"], ref["bytes"])
        # All executable/object/dependency-source references remain hash records.
        omitted = ".olean" in path.name or path.suffix == ".gz" or \
            (path.is_relative_to(self.repo / ".lake/packages")) or \
            "/bin/" in str(path)
        if not omitted:
            self.include(path, category)

    def tree(self, root, category):
        require(root.is_dir(), f"Missing evidence directory: {root}")
        for path in sorted(root.rglob("*")):
            if path.is_file() and path.suffix in TEXT_SUFFIXES:
                if path.is_symlink():
                    target = path.resolve(strict=True)
                    require(target.is_relative_to(self.workspace) and target.is_file(),
                            f"Evidence alias resolves outside workspace: {path}")
                    self.aliases[path] = {"original_path": str(path),
                                          "link_text": str(path.readlink()),
                                          "resolved_path": str(target)}
                    self.include(target, category)
                else:
                    self.include(path, category)

    def recheck(self):
        for path, record in list(self.watched.items()):
            self.watch(path, record["sha256"], record["bytes"])
        for path, record in self.aliases.items():
            require(path.is_symlink() and str(path.readlink()) == record["link_text"] and
                    str(path.resolve(strict=True)) == record["resolved_path"],
                    f"Evidence alias changed during collection: {path}")


def collect(workspace):
    repo = workspace / "goldbach-formalization"
    runtime = workspace / "lean-runtime"
    owned = repo / "verification/parts/p1/round2/permit"
    inputs = Inputs(workspace, repo, runtime)
    receipt_path = runtime / "part1-permit-final-receipt.json"
    inputs.include(receipt_path, "current-permit-final-receipt")
    receipt = json.loads(receipt_path.read_text())
    require(receipt["status"] == "VERIFIED", "Receipt has not passed its actual gates")
    require(list(receipt["targets"]) == TARGETS, "Wrong target scope")
    verification = receipt["verification"]
    require(verification["actual_original_frontend_compilation"] is True and
            verification["frontend_api"] == "Lean.Elab.runFrontend" and
            verification["trustLevel"] == 0 and verification["target_warning_as_error"] is True and
            verification["metadata_adapter_during_compilation_or_replay"] is False and
            verification["standard_lake_build_executed"] is False and
            verification["full_repository_build_or_replay_executed"] is False,
            "Unexpected validation mode")
    require(verification["original_leanchecker_three_sequential_calls_aggregate_exit_code"] == 0 and
            verification["original_leanchecker_individual_exit_codes"] == dict.fromkeys(TARGETS, 0),
            "Incomplete original-checker success")

    closure = receipt["closure"]
    require((closure["source_modules"], closure["local_source_modules"],
             closure["official_cached_source_modules"], closure["newly_compiled_local_modules"],
             closure["reused_archived_local_modules"]) == (3384, 16, 3368, 3, 13),
            "Unexpected permit closure census")
    for ref in refs(receipt):
        inputs.reference(ref, "current-receipt-reference")
    result = json.loads(Path(closure["result"]["path"]).read_text())
    require(result == closure["execution_result"] and result["returncode"] == 0 and
            result["status"] == "SUCCEEDED" and result["targets"] == TARGETS and
            result["complete_local_modules"] == 16,
            "Actual compilation result is incomplete or stale")
    state = json.loads(Path(closure["state"]["path"]).read_text())
    plan = json.loads(Path(closure["plan"]["path"]).read_text())
    require(len(state) == 16 and set(state) == set(plan["local_modules"]), "Local state mismatch")
    for module in TARGETS:
        item = receipt["targets"][module]
        require(item["returncode"] == item["trustLevel"] == 0 and item["strict"] is True and
                item["metadata_adapter"] is False and item["compiled_in_permit"] is True and
                item["original_checker_replayed_defined_declarations"] is True and
                item["source_sha256_before"] == item["source_sha256_after"] == SOURCES[module] and
                item["source"]["sha256"] == SOURCES[module] and
                item["attempt_source_snapshot"]["sha256"] == SOURCES[module],
                f"Incomplete or changed target: {module}")
        require(state[module]["olean_sha256"] == item["olean_sha256"], f"Object mismatch: {module}")
        text = Path(item["log"]["path"]).read_text()
        require(text.splitlines().count("FRONTEND_OK module=" + module + " trustLevel=0") == 1,
                f"Missing actual frontend success marker: {module}")

    replay = receipt["replay"]
    require(replay["status"] == "SUCCEEDED" and replay["verified"] is True and
            replay["returncode"] == 0 and replay["observed_replay_lines"] == TARGETS and
            replay["expected_targets"] == TARGETS and len(replay["calls"]) == 3,
            "Wrong replay coverage")
    checker = receipt["toolchain"]["binaries_rechecked"]["leanchecker"]
    require(replay["commands"] == [[checker["path"], "--verbose", m] for m in TARGETS],
            "Unexpected checker invocation")
    for item, module in zip(replay["calls"], TARGETS):
        require(item["module"] == module and item["returncode"] == 0 and
                item["observed_replay_lines"] == [module], f"Missing individual replay: {module}")
        inputs.watch(item["log"], item["log_sha256"])
        inputs.include(item["log"], "actual-original-checker-log")
    inputs.watch(replay["log"], replay["log_sha256"])
    inputs.include(replay["log"], "actual-original-checker-aggregate-log")

    audit = receipt["audit"]
    require(audit["declaration_count"] == 36 and audit["module_counts"] == MODULE_COUNTS and
            set(audit["allowed_axioms"]) == set(audit["observed_axioms"]) == ALLOWED,
            "Wrong audit census or axiom scope")
    lines = Path(audit["full_types_in_raw_audit_log"]["path"]).read_text().splitlines()
    rows = [json.loads(line.split(" ", 1)[1]) for line in lines
            if line.startswith("PART1_STORED_CAP_AUDIT_DECL ")]
    by_name = {row["name"]: row for row in rows}
    require(len(rows) == len(by_name) == 36 and
            by_name == {row["name"]: row for row in audit["declarations"]},
            "Raw audit declarations differ from receipt")
    require(lines.count("PART1_STORED_CAP_AUDIT_COUNT 36") == 1, "Missing raw census count")
    for row in rows:
        require(row["module"] in MODULE_COUNTS and row["kind"] != "axiom" and
                set(row["axioms"]) <= ALLOWED, f"Forbidden audit entry: {row['name']}")

    bindings = json.loads(Path(closure["dependency_bindings"]["path"]).read_text())
    require(bindings["targets"] == TARGETS and bindings["source_module_count"] == 3384 and
            len(bindings["local_modules"]) == 16 and len(bindings["cached_modules"]) == 3368,
            "Wrong dependency binding scope")
    for ref in refs(bindings):
        inputs.reference(ref, "permit-supplier-source-object-or-original-log")
    require(all(pin["exact_pin"] is True and not pin["tracked_changes"] and
                pin["expected_rev"] == pin["actual_head"] for pin in receipt["dependency_pins"]),
            "Changed dependency pin")

    # Original attempt records are embedded verbatim, including recovery failures.
    # They are not interpreted as successful target compilations.
    inputs.tree(runtime / "logs/round2/permit", "independent-permit-original-runtime-record")
    inputs.tree(runtime / "logs/round2/cache", "official-cache-restoration-attempt-record")
    inputs.tree(runtime / "logs/round2/bootstrap", "official-cache-bootstrap-record-not-new-permit-proof")
    inputs.tree(runtime / "recovery", "toolchain-and-pinned-dependency-restoration-record")
    for path in [runtime / "round2_bootstrap_cache.py", runtime / "round2_get_cache.py",
                 runtime / "cache-metadata-bin/lean"]:
        inputs.include(path, "cache-bootstrap-or-metadata-only-driver-source")
    for path in [runtime / "cache-driver/lakefile.lean", runtime / "cache-driver/roots.txt",
                 runtime / "cache-driver/lake-manifest.json", runtime / "runtime-probe.json"]:
        if path.is_file():
            inputs.include(path, "restored-runtime-or-cache-driver-configuration")
    semantics = replay["semantics"]
    inputs.watch(semantics["source_path"], semantics["source_sha256"])
    inputs.include(semantics["source_path"], "original-checker-semantics-source")
    for name in ["KEY_THEOREM_TYPES.md", "check.sh", "INTEGRATION.patch", "archive_evidence.py"]:
        inputs.include(owned / name, "owned-type-inventory-or-reproduction-source")
    inputs.recheck()

    manifest = {
        "kind": "Original independent P1 stored-cap permit evidence; no compiled binaries embedded",
        "receipt_sha256": inputs.watched[receipt_path]["sha256"],
        "verified_targets": TARGETS,
        "target_source_sha256": SOURCES,
        "actual_audit_module_counts": MODULE_COUNTS,
        "source_modules": 3384,
        "new_compilations": 3,
        "original_checker_calls": 3,
        "reused_local_suppliers": 13,
        "official_cached_suppliers": 3368,
        "uncompiled_historical_integral_targets_included_in_success": False,
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
    payloads["MANIFEST.json"] = encoded(manifest)
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
                    f"Archive payload mismatch: {entry.name}")
    inputs.recheck()
    temporary.replace(output)
    summary = {"status": "ARCHIVED_VERIFIED_PERMIT_EVIDENCE", "path": str(output),
               "sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
               "bytes": output.stat().st_size, "member_count": len(payloads),
               "payload_bytes": sum(map(len, payloads.values())),
               "receipt_sha256": inputs.watched[receipt_path]["sha256"],
               "verified_reference_count": len(inputs.watched),
               "binaries_embedded": False,
               "scope": "Only the independent three-target permit milestone"}
    (owned / "ARTIFACT.json").write_bytes(encoded(summary))
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", required=True, type=Path)
    collect(parser.parse_args().workspace.resolve())
