#!/usr/bin/env python3
"""Check frozen P3.2 historical reuse evidence; never invoke Lean or write files."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs/part3-distribution/node32-20261125/HISTORICAL_REUSE.json"
HISTORY_COMMIT = "10b89181754c78c0e77616677295ee2105de0bb6"
REPOSITORY = "https://github.com/UyNewNas/goldbach-formalization"
EXPECTED_SNAPSHOT_SHA256 = "1eb6736338866b18e1e980e6fcda108e7d2e7a0763143c816e8eadf0adedcd83"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMMENT_VARIANT = "ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson"
IMPORT_RE = re.compile(r"^import[ \t]+([A-Za-z0-9_.]+)[ \t\r]*$", re.MULTILINE)


class VerificationError(ValueError):
    """A source or historical evidence binding failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def relative_file(root, path):
    rel = Path(path)
    require(not rel.is_absolute() and ".." not in rel.parts, f"non-relative path: {path}")
    return root / rel


def checked_json(root, reference):
    path = relative_file(root, reference["path"])
    raw = path.read_bytes()
    require(sha256(raw) == reference["sha256"], f"evidence hash mismatch: {path}")
    return json.loads(raw)


def declaration_summary(records, module):
    """Inspect the full historical types, not a source-level declaration count."""
    require(bool(records), f"empty declaration inventory: {module}")
    names = []
    axioms = set()
    for row in records:
        require(row["module"] == module, f"declaration module mismatch: {module}")
        require(isinstance(row.get("name"), str) and row["name"], f"missing name: {module}")
        names.append(row["name"])
        for flag in ("unsafe", "partial", "axiom"):
            require(row.get(flag) is False, f"unsafe declaration flag {flag}: {row['name']}")
        typ = row.get("type")
        require(isinstance(typ, str) and bool(typ.strip()) and "⋯" not in typ,
                f"empty or truncated declaration type: {row['name']}")
        dependencies = row.get("axioms")
        require(isinstance(dependencies, list) and all(
            isinstance(x, str) and x in STANDARD_AXIOMS for x in dependencies),
            f"forbidden transitive axiom: {row['name']}")
        axioms.update(dependencies)
    require(len(names) == len(set(names)), f"duplicate module-local records: {module}")
    ordered = sorted(records, key=lambda row: row["name"])
    return {
        "historical_record_count": len(records),
        "full_records_canonical_sha256": sha256(canonical(ordered)),
        "full_types_canonical_sha256": sha256(canonical(
            [{"name": row["name"], "type": row["type"]} for row in ordered])),
        "transitive_axioms": sorted(axioms),
        "unsafe": 0, "partial": 0, "axiom": 0,
        "empty_or_truncated_types": 0,
    }


def audit_summary(receipt, module, source_hash, object_parts, record_count):
    require(receipt.get("status") == "PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS",
            f"historical audit did not pass: {module}")
    require(receipt.get("targets", {}).get(module) == source_hash,
            f"historical audit target source mismatch: {module}")
    before, after = receipt["inputs_before"], receipt["inputs_after"]
    require(before == after, f"historical audit before/after mismatch: {module}")
    require(before["sources"].get(module) == source_hash,
            f"historical audit input source mismatch: {module}")
    require(before["owned_object_parts"].get(module) == object_parts,
            f"historical audit object mismatch: {module}")
    require(receipt["declaration_counts"].get(module) == record_count,
            f"historical audit declaration count mismatch: {module}")
    replays = [s for s in receipt["stages"]
               if s.get("kind") == "stock_replay" and s.get("module") == module]
    inventories = [s for s in receipt["stages"]
                   if s.get("kind") == "full_inventory_type_axioms"]
    require(len(replays) == 1 and len(inventories) == 1,
            f"historical audit stage inventory mismatch: {module}")
    replay, inventory = replays[0]["result"], inventories[0]
    require(replay.get("status") == "PASS" and replay.get("returncode") == 0,
            f"historical stock replay did not pass: {module}")
    require(inventory.get("exit_code") == 0,
            f"historical type/axiom inventory did not pass: {module}")
    replay_command = replay.get("command", [])
    require(len(replay_command) >= 2
            and Path(replay_command[0]).name == "leanchecker"
            and replay_command[-1] == module, f"unexpected historical replay command: {module}")
    require("-DwarningAsError=true" in inventory.get("command", []),
            f"historical type audit lacks warning-as-error option: {module}")
    require(receipt.get("external_closure_replay_claimed") is False
            and receipt.get("unconditional_main_claimed") is False,
            f"unexpected historical trust boundary: {module}")
    return {
        "status": receipt["status"],
        "source_sha256": source_hash,
        "object_parts": object_parts,
        "historical_record_count": record_count,
        "inputs_canonical_sha256": sha256(canonical(before)),
        "stock_replay": {
            "status": replay["status"], "returncode": replay["returncode"],
            "command": replay_command, "log_sha256": replay["log_sha256"],
        },
        "full_inventory_type_axioms": {
            "exit_code": inventory["exit_code"], "command": inventory["command"],
            "log_sha256": inventory["log_sha256"],
        },
    }


def without_first_documentation_header(raw):
    """The one frozen Physical module exception; not a general comment normalizer."""
    start = raw.find(b"/-!")
    require(start >= 0, "Physical module documentation header missing")
    stop = raw.find(b"-/", start + 3)
    require(stop >= 0 and b"/-" not in raw[start + 3:stop],
            "Physical module documentation header is not the reviewed simple block")
    return raw[:start] + raw[stop + 2:]


def verify_snapshot_structure(snapshot):
    require(snapshot.get("schema") == "p3-node32-historical-reuse-v1", "unexpected schema")
    require(snapshot.get("status") == "HISTORY_SOURCE_MATCH_ONLY", "invalid status claim")
    require(snapshot.get("historical_commit") == HISTORY_COMMIT, "historical commit mismatch")
    scope = snapshot["scope"]
    require(scope["trust_mode"] == "NORMAL_IMPORTED_ENVIRONMENT_TRUST", "trust mode mismatch")
    for flag in ("new_compilation", "new_kernel_replay", "node_complete",
                 "full_import_closure_replayed", "external_closure_replayed"):
        require(scope.get(flag) is False, f"invalid scope claim: {flag}")
    require(scope.get("new_declarations") == 0, "historical records counted as new declarations")
    modules = snapshot["modules"]
    require(len(modules) == 130 and len(snapshot["targets"]) == 6, "frozen closure size mismatch")
    require(len(set(snapshot["targets"])) == 6, "duplicate target")
    owned = [x for x in modules.values() if x["evidence_kind"] == "historical_owned"]
    trusted = [x for x in modules.values() if x["evidence_kind"] == "trusted_import_source_binding"]
    require(len(owned) == 89 and len(trusted) == 41, "owned/imported boundary mismatch")
    require(len(snapshot["audit_receipts"]) == 72, "original receipt inventory mismatch")
    for module, ent in modules.items():
        require(ent["path"] == module.replace(".", "/") + ".lean",
                f"source path/module mismatch: {module}")
        source_ref = ent["historical_source"]
        expected_url = f"{REPOSITORY}/blob/{HISTORY_COMMIT}/{ent['path']}"
        require(source_ref["url"] == expected_url, f"historical source URL mismatch: {module}")
        if ent["source_relation"] == "exact_historical_bytes":
            require(ent["source_sha256"] == source_ref["sha256"],
                    f"false exact historical source claim: {module}")
        else:
            require(module == COMMENT_VARIANT
                    and ent["source_relation"] == "retained_baseline_documentation_header",
                    f"unapproved source variant: {module}")
        if ent["evidence_kind"] != "historical_owned":
            require("census_entry" not in ent and "declarations" not in ent,
                    f"trusted import given owned credit: {module}")
            continue
        record, summary = ent["census_entry"], ent["declarations"]
        require(record["module"] == module
                and record["source_sha256"] == source_ref["sha256"],
                f"census/source mismatch: {module}")
        require(summary["historical_record_count"] == record["complete_serialized_declarations"],
                f"historical declaration count mismatch: {module}")
        require(all(summary[x] == 0 for x in
                    ("unsafe", "partial", "axiom", "empty_or_truncated_types")),
                f"unsafe compact declaration summary: {module}")
        require(set(summary["transitive_axioms"]) <= STANDARD_AXIOMS,
                f"forbidden compact transitive axioms: {module}")
        audit = snapshot["audit_receipts"][record["owned_receipt_sha256"]]
        check = audit["module_checks"][module]
        require(check["source_sha256"] == record["source_sha256"]
                and check["object_parts"] == record["object_parts"]
                and check["historical_record_count"] == record["complete_serialized_declarations"],
                f"compact receipt binding mismatch: {module}")
    for receipt_hash, ent in snapshot["audit_receipts"].items():
        ref = ent["reference"]
        require(ref["sha256"] == receipt_hash, "receipt digest/key mismatch")
        require(ref["url"] == f"{REPOSITORY}/blob/{HISTORY_COMMIT}/{ref['path']}",
                "historical receipt URL mismatch")


def verify_sources(snapshot, root, metadata_root):
    modules = snapshot["modules"]
    imports = {}
    for module, ent in modules.items():
        path = relative_file(root, ent["path"])
        raw = path.read_bytes()
        require(sha256(raw) == ent["source_sha256"], f"source hash mismatch: {ent['path']}")
        imports[module] = sorted(IMPORT_RE.findall(raw.decode("utf-8")))
        require(imports[module] == ent["direct_imports"], f"source import mismatch: {module}")
    for name, digest in snapshot["pins"].items():
        require(sha256(relative_file(root, name).read_bytes()) == digest,
                f"project pin mismatch: {name}")
    reached, queue = set(), list(snapshot["targets"])
    while queue:
        name = queue.pop()
        if name in reached:
            continue
        require(name in modules, f"project import missing from frozen closure: {name}")
        reached.add(name)
        queue.extend(x for x in imports[name] if x.startswith("ImbalancedChen."))
    require(reached == set(modules), "six-target project closure differs from frozen 130 modules")

    reused = checked_json(metadata_root, snapshot["source_selection"])
    require(reused["source_commit"] == HISTORY_COMMIT
            and reused["targets"] == snapshot["targets"], "source-selection provenance mismatch")
    require(len(reused["records"]) == 73, "source-selection module count mismatch")
    for ent in reused["records"]:
        require(ent["sha256"] == modules[ent["module"]]["source_sha256"],
                f"source-selection hash mismatch: {ent['module']}")

    aggregate = checked_json(metadata_root, snapshot["current_import_binding"])
    bindings = {}
    for ent in aggregate["modules"]:
        for path, digest in ent.get("local_import_sha256", {}).items():
            bindings.setdefault(path, set()).add(digest)
    for module, ent in modules.items():
        if ent["evidence_kind"] == "trusted_import_source_binding":
            require(bindings.get(ent["path"]) == {ent["source_sha256"]},
                    f"existing aggregate import-source mismatch: {module}")
    baseline = checked_json(metadata_root, snapshot["retained_variant"]["baseline_report"])
    variant = modules[COMMENT_VARIANT]
    require(baseline["source_sha256"][variant["path"]] == variant["source_sha256"],
            "retained Physical source does not match existing baseline report")


def recheck_original_evidence(snapshot, source_root, evidence_root):
    originals = {name: checked_json(evidence_root, ref)
                 for name, ref in snapshot["evidence"].items()}
    archive, plan = originals["archive_manifest"], originals["source_plan"]
    acceptance, census = originals["acceptance"], originals["census"]
    declarations = originals["declarations"]
    refs = snapshot["evidence"]
    require(plan["archive_manifest_sha256"] == refs["archive_manifest"]["sha256"],
            "historical plan/manifest mismatch")
    payload_hashes = {entry["sha256"] for entry in archive["payloads"]}
    require(all(refs[name]["sha256"] in payload_hashes
                for name in ("acceptance", "census", "declarations")),
            "historical payloads not bound by archive manifest")
    require(acceptance["status"] == "ROOT_AFTER260_NEXT6_TERMINAL_ACCEPTED",
            "historical root acceptance missing")
    require(acceptance["current_census"]["sha256"] == refs["census"]["sha256"]
            and acceptance["complete_declarations"]["sha256"] == refs["declarations"]["sha256"],
            "root acceptance does not bind selected census/declarations")
    require(acceptance["trust_mode"] == "NORMAL_IMPORTED_ENVIRONMENT_TRUST"
            and acceptance["project_import_closure_replayed"] is False
            and acceptance["external_closure_replayed"] is False,
            "historical acceptance boundary mismatch")
    grouped = {}
    for row in declarations:
        if row["module"] in snapshot["modules"]:
            grouped.setdefault(row["module"], []).append(row)
    receipts = {digest: checked_json(evidence_root, info["reference"])
                for digest, info in snapshot["audit_receipts"].items()}
    selected_records = []
    for module, ent in snapshot["modules"].items():
        historical = relative_file(evidence_root, ent["path"]).read_bytes()
        require(sha256(historical) == ent["historical_source"]["sha256"],
                f"historical source hash mismatch: {module}")
        if ent["source_relation"] != "exact_historical_bytes":
            selected = relative_file(source_root, ent["path"]).read_bytes()
            require(without_first_documentation_header(historical)
                    == without_first_documentation_header(selected),
                    "Physical source differs outside the frozen documentation header")
        if ent["evidence_kind"] != "historical_owned":
            require(module not in census["modules"], f"incorrect trusted-import classification: {module}")
            continue
        record = census["modules"][module]
        require(record == ent["census_entry"], f"original census extraction mismatch: {module}")
        rows = grouped[module]
        require(declaration_summary(rows, module) == ent["declarations"],
                f"original full declaration extraction mismatch: {module}")
        selected_records.extend(rows)
        receipt_hash = record["owned_receipt_sha256"]
        summary = audit_summary(receipts[receipt_hash], module, record["source_sha256"],
                                record["object_parts"], record["complete_serialized_declarations"])
        require(summary == snapshot["audit_receipts"][receipt_hash]["module_checks"][module],
                f"original audit extraction mismatch: {module}")
    require(len(selected_records) == snapshot["historical_records_reused"]
            and len({row["name"] for row in selected_records}) == snapshot["historical_fullnames_reused"],
            "historical declaration totals mismatch")
    return len(receipts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    parser.add_argument("--evidence-root", type=Path,
                        help="Optional original evidence tree; recheck all 72 raw historical receipts.")
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    args = parser.parse_args()
    try:
        raw = args.manifest.read_bytes()
        require(sha256(raw) == EXPECTED_SNAPSHOT_SHA256, "frozen snapshot hash mismatch")
        snapshot = json.loads(raw)
        verify_snapshot_structure(snapshot)
        verify_sources(snapshot, args.source_root, ROOT)
        rechecked = 0
        if args.evidence_root is not None:
            rechecked = recheck_original_evidence(snapshot, args.source_root, args.evidence_root)
        print(json.dumps({
            "status": "HISTORY_SOURCE_MATCH_ONLY",
            "project_modules": 130,
            "historical_owned_modules": 89,
            "exact_historical_owned_source_matches": 88,
            "retained_documentation_header_variants": 1,
            "trusted_import_modules": 41,
            "historical_records_reused": snapshot["historical_records_reused"],
            "historical_fullnames_reused": snapshot["historical_fullnames_reused"],
            "original_audit_receipts_in_snapshot": 72,
            "original_audit_receipts_rechecked": rechecked,
            "evidence_mode": "ORIGINAL_BYTES_RECHECKED" if args.evidence_root else "FROZEN_COMPACT_EXTRACTION",
            "new_compilation": False, "new_kernel_replay": False, "new_declarations": 0,
            "current_objects_verified": False,
            "full_import_closure_replayed": False, "external_closure_replayed": False,
            "node_complete": False,
            "trust_mode": "NORMAL_IMPORTED_ENVIRONMENT_TRUST",
            "snapshot_sha256": sha256(raw),
        }, indent=2))
        return 0
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({"status": "HISTORY_REUSE_CHECK_FAILED", "error": str(exc),
                          "new_compilation": False, "node_complete": False}, indent=2))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
