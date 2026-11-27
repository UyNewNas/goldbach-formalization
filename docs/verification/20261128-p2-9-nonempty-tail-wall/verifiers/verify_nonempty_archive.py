#!/usr/bin/env python3
"""Independently verify sealed NonemptyTailWallCount evidence, without execution.

Only reads original evidence. Never extracts the archive, runs archived code,
imports its Python modules, invokes Lean, or assigns root acceptance. The only
write is a new --output JSON file. Supply archive pins from the original task's
transport result, not from a transport document inside the archive.
"""
from __future__ import annotations
import argparse
import ast
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile

MODULE = "ImbalancedChen.P2FiniteMarkedGamma5NonemptyTailWallCount"
SOURCE_SHA256 = "1d95db22b754d89b3d7336d6c66b64733bd7600aab5d22ed53a5f5b1d5294e1a"
SOURCE_GIT_BLOB = "eaaa2b2d78c26668c3c4d54dca00876cd5bc1c8a"
RECOVERY_SHA256 = "06d070dcd65ce8fc7e7299ea0b78198294adbdda11489293223b32f5e343f90c"
OWNED_DRIVER_SHA256 = "f502dc224678c54830a049671d90ecc98c5f615d55fae84dbb75f7d6840dfe88"
PROBE_PINS = {
    "nonempty-direct-imports": "7456340732cd4ef2aa138b32d211d6bab7950ccd1c97e7d28ae4cd522d1f17d9",
    "consumer-actual-imports": "be1d3885c8fb2cc295ae152450a651f8027711ad87f3e9377ccaf6a24c9e6ea1",
}
TOOLS = {
    "ci_runtime_guard.py": "837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877",
    "run_guarded.py": "c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526",
    "validate_member_roots_owned.py": "ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201",
}
RUN_PINS = {
    "old_manifest_sha256": "9c6092358690df4615ae8f99f2383e06528f18077b25448c2a724569ac393a02",
    "old_actual_imports_sha256": "9ca216b1d0c19c50050f2d16028359ceb42d6f3f3f2fc4ac10a9d389413de8f8",
    "input_index_sha256": "2b8b20b150f16b54c1be3ccb39df33f292c92767ef1f94bbd011b9a6536cce7f",
    "reception_receipt_sha256": "1104d485e61164f2b2c1eb6e7c7a06ac4af212599cec0c511f0299106d17d6c3",
    "original_helper_controller_sha256": "f509c0fec28d99291ee224920dadb68958cbaa6f243100e7e3696ebbdd2805ea",
}
HELPER_PINS = {
    "stamp": "23e6774cd954f1d0ab8b9f9241add325ca142a4b9fc479a45324883f8107d8b1",
    "save": "ac08488f13a491453135185ed8f92ff2dd3aff6a98538ff42405bbbe24b43b2c",
    "utc": "9f680e20ae07796a69479c21d1e311a0aa5004f745a875be2756f9c7dbbed535",
    "stage": "535c7ef8ced99dcfac3641213d33c606e04d8f0e9fe45515844a2739de2c825e",
    "compile_audit_text": "d69d63bf2bd39d4afaa96bffae16363c8f05d699520f24c554ec657178d463b8",
    "named_kernel": "ff95c9f656c3b8d4b3cf3ae7e5f54497a39d6b2daabcdae3d6f2221dec9b529d",
    "full_owned": "e943875a8350d4108ec72045808d6aab3ff9e99fbcfee0bffc415ec2150c5518",
    "AUDIT_TEMPLATE": "79207198e3b229b48e7e5385f5b496cad3507fde975551b15d8edee4688d92a1",
}
OLD_BASE = "/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77"
PIN = "leanprover/lean4:v4.33.0-rc1"
REALBIN = "/workspace/toolchains/lean-4.33.0-rc1-linux/bin"
POLICY = "Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2"
ALLOWED_AXIOMS = frozenset({"Classical.choice", "Quot.sound", "propext"})
FACETS = frozenset({".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"})
STAGES = ("runtime-initial-audit", "nonempty-direct-imports", "normal-build", "consumer-actual-imports", "named-kernel", "full-owned", "runtime-final-audit")
MANIFEST_SCHEMA = "p29_nonempty_complete_single_target_evidence_v1"
RESULT = "PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED"
CHUNK = 1024 * 1024
CAPTURE_LIMIT = 128 * 1024 * 1024
TOTAL_CAPTURE_LIMIT = 384 * 1024 * 1024
SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
CONFIG_MEMBERS = {"project/lean-toolchain", "project/lakefile.toml", "project/lake-manifest.json"}

@dataclass(frozen=True)
class Pins:
    archive_bytes: int
    archive_sha256: str
    manifest_sha256: str
    members: int

class VerificationError(Exception):
    def __init__(self, code: str, detail: str):
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")

def require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise VerificationError(code, detail)

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def hash_file(path: Path) -> dict:
    h = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(CHUNK), b""):
            size += len(block)
            h.update(block)
    return {"bytes": size, "sha256": h.hexdigest()}

def strict_json(data: bytes | str, label: str):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate_json_key", f"{label}: {key}")
            result[key] = value
        return result

    def invalid(value):
        raise VerificationError("invalid_json_constant", f"{label}: {value}")

    try:
        return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError("invalid_json", f"{label}: {error}") from error

def canonical_member(name: str) -> str:
    require(isinstance(name, str) and bool(name), "unsafe_member_path", repr(name))
    p = PurePosixPath(name)
    require(not p.is_absolute() and "\\" not in name and "\x00" not in name
            and not re.match(r"^[A-Za-z]:", name)
            and all(part not in {"", ".", ".."} for part in name.split("/"))
            and str(p) == name,
            "unsafe_member_path", repr(name))
    return name

@dataclass
class Evidence:
    members: dict
    captured: dict
    manifest: dict
    manifest_name: str
    archive_identity: dict

    def name(self, suffix: str) -> str:
        hits = [name for name in self.members
                if name == suffix or name.endswith("/" + suffix)]
        require(len(hits) == 1, "missing_or_ambiguous_member", f"{suffix}: {hits}")
        return hits[0]

    def raw(self, suffix: str) -> bytes:
        name = self.name(suffix)
        require(name in self.captured, "uncaptured_member", name)
        return self.captured[name]

    def json(self, suffix: str):
        return strict_json(self.raw(suffix), suffix)

def read_archive(path: Path, pins: Pins) -> Evidence:
    identity = hash_file(path)
    require(identity["bytes"] == pins.archive_bytes, "archive_bytes_mismatch", str(identity))
    require(identity["sha256"] == pins.archive_sha256, "archive_sha256_mismatch", str(identity))
    members = {}
    captured = {}
    capture_total = 0
    try:
        with tarfile.open(path, "r|*") as archive:
            for member in archive:
                name = canonical_member(member.name)
                require(name not in members, "duplicate_tar_member", name)
                require(member.type in (tarfile.REGTYPE, tarfile.AREGTYPE)
                        and not member.issparse() and not member.linkname,
                        "unsafe_member_type", f"{name}: {member.type!r}")
                require(len(members) < pins.members, "extra_tar_member", name)
                keep = name.endswith((".json", ".jsonl", ".log", ".lean", ".py")) or name in CONFIG_MEMBERS
                require(not keep or member.size <= CAPTURE_LIMIT,
                        "capture_limit", f"{name}: {member.size}")
                h = hashlib.sha256()
                size = 0
                data = io.BytesIO() if keep else None
                stream = archive.extractfile(member)
                require(stream is not None, "unreadable_member", name)
                with stream:
                    for block in iter(lambda: stream.read(CHUNK), b""):
                        size += len(block)
                        h.update(block)
                        if data is not None:
                            data.write(block)
                require(size == member.size, "truncated_member", name)
                members[name] = {"bytes": size, "sha256": h.hexdigest()}
                if data is not None:
                    capture_total += size
                    require(capture_total <= TOTAL_CAPTURE_LIMIT, "capture_limit", "total")
                    captured[name] = data.getvalue()
    except (tarfile.TarError, EOFError) as error:
        raise VerificationError("invalid_tar", str(error)) from error

    require(len(members) == pins.members, "member_count_mismatch", str(len(members)))
    manifests = [name for name in members if PurePosixPath(name).name == "FILE_MANIFEST.json"]
    require(len(manifests) == 1, "manifest_count_mismatch", str(manifests))
    manifest_name = manifests[0]
    require(members[manifest_name]["sha256"] == pins.manifest_sha256,
            "manifest_sha256_mismatch", manifest_name)
    manifest = strict_json(captured[manifest_name], manifest_name)
    require(isinstance(manifest, dict) and manifest.get("schema") == MANIFEST_SCHEMA,
            "manifest_schema_mismatch", manifest_name)
    files = manifest.get("files")
    require(isinstance(files, dict), "manifest_files_schema", "expected files object")
    for name, record in files.items():
        canonical_member(name)
        require(isinstance(record, dict)
                and type(record.get("bytes")) is int and record["bytes"] >= 0
                and isinstance(record.get("sha256"), str)
                and SHA256_RE.fullmatch(record["sha256"]) is not None,
                "manifest_record_schema", name)
    require(set(files) == set(members) - {manifest_name}, "manifest_member_set_mismatch",
            json.dumps({"unmanifested": sorted(set(members) - {manifest_name} - set(files)),
                        "absent": sorted(set(files) - set(members))}, sort_keys=True))
    for name in sorted(files):
        require(members[name] == {key: files[name][key] for key in ("bytes", "sha256")},
                "member_identity_mismatch", name)
    return Evidence(members, captured, manifest, manifest_name, identity)


def parse_owned(raw: bytes, actual_exit: int = 0) -> tuple[list, dict, list]:
    """Independently parse the raw audit, reproducing the original inventory.

    No code from the archive is imported or executed. The bound Lean driver
    rejects unsafe and axiom declarations before emitting each record.
    """
    lines = raw.decode("utf-8").splitlines()
    prefixes = ("MEMBER_OWNED_NAMES ", "MEMBER_OWNED_DECL ",
                "MEMBER_OWNED_MODULE ", "MEMBER_OWNED_COUNT ")
    parsed = {prefix: [] for prefix in prefixes}
    for line in lines:
        if not line.strip():
            continue
        prefix = next((p for p in prefixes if line.startswith(p)), None)
        require(prefix is not None, "unrecognized_owned_log_line", line[:160])
        parsed[prefix].append(strict_json(line[len(prefix):], prefix.strip()))
    inventories = parsed[prefixes[0]]
    declarations = parsed[prefixes[1]]
    counts = parsed[prefixes[2]]
    totals = parsed[prefixes[3]]
    require(len(inventories) == 1 and isinstance(inventories[0], dict),
            "raw_inventory_count", str(len(inventories)))
    names = inventories[0].get("names")
    require(isinstance(names, list) and all(isinstance(name, str) for name in names)
            and len(names) == len(set(names)) > 0, "raw_inventory_names", "expected a nonempty unique inventory")
    count = len(names)
    require(len(totals) == 1 and type(totals[0]) is int and totals[0] == count
            and len(declarations) == count, "raw_total_mismatch", str(totals))
    require(counts == [{"count": count, "module": MODULE}], "raw_module_count_mismatch", str(counts))
    require(all(isinstance(row, dict) for row in declarations), "declaration_schema", "expected objects")
    require([row.get("name") for row in declarations] == names,
            "raw_declaration_name_order_mismatch", "raw inventory versus declarations")
    allowed_kinds = {"theorem", "definition", "opaque", "quotient", "inductive", "constructor", "recursor"}
    for row in declarations:
        name = row["name"]
        require(row.get("module") == MODULE, "declaration_owner_mismatch", name)
        require(row.get("kind") in allowed_kinds and not row.get("unsafe", False)
                and not row.get("is_unsafe", False), "unsafe_or_axiom_declaration", name)
        require(type(row.get("is_private")) is bool
                and row["is_private"] == name.startswith("_private."), "private_flag_mismatch", name)
        require(isinstance(row.get("type"), str) and bool(row["type"])
                and isinstance(row.get("type_expression"), str)
                and row["type_expression"].startswith("Lean.Expr."), "declaration_type_schema", name)
        require(all(token not in row[key] for key in ("type", "type_expression")
                    for token in ("⋯", "...")), "truncated_declaration_type", name)
        universes = row.get("universe_parameters")
        axioms = row.get("axioms")
        require(isinstance(universes, list) and all(isinstance(x, str) for x in universes),
                "universe_parameters_schema", name)
        require(isinstance(axioms, list) and all(isinstance(x, str) for x in axioms)
                and set(axioms) <= ALLOWED_AXIOMS, "forbidden_axiom", name)
    observed_axioms = sorted({axiom for row in declarations for axiom in row["axioms"]})
    inventory = {
        "schema": "member_ten_roots_complete_owned_inventory_v1",
        "method": "Full env.constants.fold plus exact getModuleIdxFor? owner; moduleNames computed once. No private/generated exclusion.",
        "count": len(names), "names": names,
        "names_sha256": digest(("\n".join(names) + "\n").encode()),
        "private_name_count": sum(row["is_private"] for row in declarations),
        "module_counts": {MODULE: len(names)}, "actual_audit_exit_code": actual_exit,
    }
    return declarations, inventory, observed_axioms


def pinned_member(e: Evidence, name: str, expected_sha: str) -> None:
    require(e.members[e.name(name)]["sha256"] == expected_sha, "pinned_member_mismatch", name)


def check_identity_schema(row, label: str) -> None:
    require(isinstance(row, dict) and set(row) == {"path", "bytes", "sha256"}
            and isinstance(row["path"], str) and PurePosixPath(row["path"]).is_absolute()
            and type(row["bytes"]) is int and row["bytes"] >= 0
            and isinstance(row["sha256"], str) and SHA256_RE.fullmatch(row["sha256"]) is not None,
            "identity_schema", label)


def verify_run(e: Evidence, driver_sha256: str, expected_base: str, package_sha256: str) -> dict:
    run = e.json("RUN_IDENTITY.json")
    base = PurePosixPath(expected_base)
    require(base.parent == PurePosixPath("/workspace") and base.name.startswith("p29-nonempty-")
            and str(base) == expected_base, "expected_base_schema", expected_base)
    require(run.get("schema") == "p29_nonempty_exact_single_target_run_v1"
            and run.get("module") == MODULE and run.get("base") == expected_base,
            "run_identity_mismatch", expected_base)
    require(run.get("driver_sha256") == driver_sha256
            and all(run.get(key) == value for key, value in RUN_PINS.items())
            and run.get("helper_source_sha256") == HELPER_PINS, "run_pin_mismatch", "run provenance")
    require(run.get("package_relocations_sha256") == package_sha256,
            "package_relocation_external_pin_mismatch", "run provenance")
    pinned_member(e, "verification/PACKAGE_PATH_RELOCATIONS.json", package_sha256)
    pinned_member(e, "verification/driver.py", driver_sha256)
    for name, pin in TOOLS.items():
        pinned_member(e, "original-tools/" + name, pin)
    source = run.get("source", {})
    require(source.get("bytes") == 6727 and source.get("sha256") == SOURCE_SHA256
            and source.get("git_blob") == SOURCE_GIT_BLOB, "run_source_pin_mismatch", MODULE)
    return run


def verify_source_outputs(e: Evidence, base: str, check_live: bool) -> dict:
    snapshot = e.json("verification/SOURCE_AND_OUTPUTS_AFTER.json")
    require(snapshot == e.json("verification/SOURCE_AND_OUTPUTS_AFTER_NORMAL.json"),
            "source_outputs_changed_after_normal", "normal versus final")
    relative = MODULE.replace(".", "/")
    expected = {base + "/project/" + relative + ".lean": "project/" + relative + ".lean"}
    for extension in (".olean", ".ilean"):
        suffix = "project/.lake/build/lib/lean/" + relative + extension
        expected[base + "/" + suffix] = suffix
    require(isinstance(snapshot, dict) and set(snapshot) == set(expected),
            "source_output_path_set_mismatch", "target .lean/.olean/.ilean only")
    outputs = {}
    for path, name in expected.items():
        row = snapshot[path]
        check_identity_schema(row, path)
        require(row["path"] == path
                and {key: row[key] for key in ("bytes", "sha256")} == e.members[e.name(name)],
                "source_output_archive_identity_mismatch", name)
        if check_live:
            require(hash_file(Path(path)) == {key: row[key] for key in ("bytes", "sha256")},
                    "source_output_live_identity_mismatch", path)
        outputs[PurePosixPath(path).suffix] = row
    source = e.raw(expected[base + "/project/" + relative + ".lean"])
    blob = hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()
    require(len(source) == 6727 and digest(source) == SOURCE_SHA256 and blob == SOURCE_GIT_BLOB,
            "target_source_pin_mismatch", MODULE)
    return {"files": outputs, "source_git_blob": blob,
            "live_check": "PASS_THREE_TARGET_FILES" if check_live else "NOT_REQUESTED"}


def verify_owned(e: Evidence, summary: dict) -> dict:
    declarations, inventory, axioms = parse_owned(e.raw("verification/full-owned.log"))
    require(declarations == e.json("verification/full-owned-DECLARATION_TYPES_AXIOMS.json"),
            "raw_declarations_mismatch", "raw audit versus declaration JSON")
    require(inventory == e.json("verification/full-owned-INVENTORY_NAME_SET_CHECK.json")
            and inventory == summary.get("inventory"), "raw_inventory_mismatch", "raw audit versus inventories")
    require(type(summary.get("owned_count")) is int and summary["owned_count"] == len(declarations),
            "owned_count_mismatch", "derived count versus summary")
    require(axioms == summary.get("observed_axioms"), "observed_axioms_mismatch", str(axioms))
    pinned_member(e, "verification/full-owned.lean", OWNED_DRIVER_SHA256)
    return {"count": len(declarations), "private_name_count": inventory["private_name_count"],
            "names_sha256": inventory["names_sha256"], "observed_axioms": axioms,
            "raw_records_equal_saved_json": True, "unsafe_axiom_rejection_driver_bound": True}


def parse_import_log(raw: bytes, label: str) -> list:
    prefix = "P29_ACTUAL_IMPORT "
    rows = []
    for line in raw.decode("utf-8").splitlines():
        if not line.strip():
            continue
        require(line.startswith(prefix), "unrecognized_import_log_line", label + ": " + line[:120])
        rows.append(strict_json(line[len(prefix):], label))
    require(bool(rows), "empty_import_log", label)
    return rows


def graph_index(graph: dict, raw: bytes, label: str) -> tuple[dict, dict]:
    require(isinstance(graph, dict) and graph.get("schema") == "p29_nonempty_exact_actual_input_parts_v1"
            and graph.get("unknown_parts") == 0 and graph.get("supplier_proof_replays") == 0,
            "import_graph_schema", label)
    modules = graph.get("actual_modules")
    parts = graph.get("parts")
    require(isinstance(modules, list) and len(modules) > 0
            and graph.get("module_count") == len(modules) and modules == parse_import_log(raw, label),
            "raw_import_modules_mismatch", label)
    require(isinstance(parts, list) and graph.get("part_count") == len(parts), "import_part_count", label)
    by_module, by_part, paths = {}, {}, {}
    for row in modules:
        require(isinstance(row, dict) and isinstance(row.get("module"), str), "import_module_schema", label)
        name = row["module"]
        require(name not in by_module and type(row.get("is_module")) is bool
                and isinstance(row.get("direct_imports"), list)
                and all(isinstance(x, str) for x in row["direct_imports"])
                and isinstance(row.get("parts"), list), "duplicate_or_invalid_module", name)
        by_module[name], paths[name] = row, set()
    for row in parts:
        require(isinstance(row, dict) and isinstance(row.get("module"), str)
                and row.get("facet") in FACETS, "import_part_schema", label)
        key = (row["module"], row["facet"])
        require(key not in by_part and key[0] in by_module, "duplicate_or_unknown_import_part", str(key))
        identity, qualified = row.get("identity"), row.get("qualified_identity")
        check_identity_schema(identity, str(key))
        check_identity_schema(qualified, str(key) + " qualified")
        require(all(identity[field] == qualified[field] for field in ("bytes", "sha256")),
                "qualified_original_bytes_changed", str(key))
        requested = row.get("requested_path")
        require(isinstance(requested, str) and PurePosixPath(requested).is_absolute()
                and requested.endswith("/" + key[0].replace(".", "/") + key[1])
                and isinstance(row.get("authority"), str) and row["authority"] not in {"", "UNQUALIFIED"}
                and isinstance(row.get("provider"), dict), "import_part_binding_schema", str(key))
        if "stat_snapshot" in row:
            snapshot = row["stat_snapshot"]
            require(isinstance(snapshot, list) and len(snapshot) == 5
                    and all(type(value) is int and value >= 0 for value in snapshot)
                    and snapshot[2] == identity["bytes"], "current_stat_schema", str(key))
        by_part[key] = row
        paths[key[0]].add((requested, identity["path"]))
    module_names = set(by_module)
    for name, row in by_module.items():
        declared = row["parts"]
        require(all(isinstance(part, dict) and isinstance(part.get("path"), str)
                    and isinstance(part.get("resolved_path"), str) for part in declared),
                "module_part_path_schema", name)
        require(len(declared) == len(paths[name])
                and {(part["path"], part["resolved_path"]) for part in declared} == paths[name],
                "module_part_identity_set_mismatch", name)
        require(set(row["direct_imports"]) <= module_names, "import_header_unknown_module", name)
    return by_module, by_part


def compare_graphs(before_modules: dict, before_parts: dict, after_modules: dict, after_parts: dict) -> None:
    require(set(after_modules) - set(before_modules) == {MODULE}
            and set(before_modules) <= set(after_modules), "import_module_delta_mismatch", "only target may be added")
    require(set(after_parts) - set(before_parts) == {(MODULE, ".olean")}
            and set(before_parts) <= set(after_parts), "import_part_delta_mismatch", "only target .olean may be added")
    for name, row in before_modules.items():
        require(after_modules[name] == row, "old_module_graph_changed", name)
    for key, row in before_parts.items():
        require(all(row.get(field) == after_parts[key].get(field)
                    for field in ("identity", "qualified_identity", "requested_path", "authority", "provider", "stat_snapshot")),
                "old_import_part_identity_changed", str(key))


def verify_relocations(e: Evidence, before_parts: dict, summary: dict) -> dict:
    recovery_name = "verification/recovery-" + RECOVERY_SHA256 + ".json"
    pinned_member(e, recovery_name, RECOVERY_SHA256)
    recovery = e.json(recovery_name)
    observed = e.json("verification/EXACT_BYTE_RELOCATIONS.json")
    require(recovery.get("schema") == "p29_exact_old_byte_relocations_v1"
            and recovery.get("object_count") == 67 and recovery.get("old_paths_modified") == 0
            and recovery.get("lean_invocations") == 0 and recovery.get("new_formal_credit") == 0,
            "recovery_index_schema", recovery_name)
    rows = recovery.get("mappings")
    require(isinstance(rows, list) and len(rows) == 67 and isinstance(observed, dict) and len(observed) == 67,
            "recovery_mapping_count", "expected 67 original relocations")
    indexed = {}
    for row in rows:
        key = (row["module"], row["facet"])
        old, selected = row["original"], row["selected"]
        check_identity_schema(old, str(key))
        check_identity_schema(selected, str(key))
        require(key not in indexed and key in before_parts and row["facet"] == ".olean"
                and all(old[field] == selected[field] for field in ("bytes", "sha256")),
                "recovery_mapping_mismatch", str(key))
        current = observed.get(old["path"])
        require(isinstance(current, dict) and current.get("original") == old and current.get("selected") == selected
                and current.get("provenance") == row["provenance"]
                and current.get("original_observation") in {"ORIGINAL_MISSING", "ORIGINAL_STILL_EXACT"},
                "recovery_observation_mismatch", str(key))
        require(before_parts[key]["identity"] == selected and before_parts[key]["qualified_identity"] == old,
                "recovery_actual_graph_mismatch", str(key))
        indexed[key] = row
    changed = {key for key, row in before_parts.items() if row["identity"] != row["qualified_identity"]}
    require(changed == set(indexed) and summary.get("old_part_relocations") == 67,
            "unaccounted_relocation", str(sorted(changed - set(indexed))))
    return {"index_sha256": RECOVERY_SHA256, "old_objects_relocated": 67, "bytes_preserved": True}


def verify_stat_revalidations(e: Evidence, before_parts: dict) -> dict:
    document = e.json("verification/CURRENT_SAME_PATH_BYTE_REVALIDATIONS.json")
    observations = document.get("observations")
    require(document.get("schema") == "p29_same_path_original_bytes_current_stat_revalidation_v1"
            and document.get("old_actual_graph_sha256") == RUN_PINS["old_actual_imports_sha256"]
            and document.get("different_bytes_admitted") is False
            and document.get("historical_stat_not_used_as_current_baseline") is True
            and isinstance(observations, dict) and document.get("count") == len(observations),
            "same_path_revalidation_schema", "historical metadata changes")
    for path, row in observations.items():
        key = (row.get("module"), row.get("facet"))
        require(key in before_parts and row.get("identity", {}).get("path") == path
                and row.get("identity") == before_parts[key]["identity"] == before_parts[key]["qualified_identity"]
                and row.get("byte_identity_unchanged") is True and row.get("fresh_hash_stat_stable") is True
                and row.get("current_stat_snapshot") == before_parts[key].get("stat_snapshot")
                and row.get("historical_stat_snapshot") != row.get("current_stat_snapshot"),
                "same_path_revalidation_mismatch", str(key))
    return {"count": len(observations), "original_bytes_unchanged": True,
            "current_stat_bound_to_actual_pre_graph": True, "historical_stat_not_required_to_equal_current": True}


def verify_import_graphs(e: Evidence, summary: dict, outputs: dict) -> dict:
    labels = ("nonempty-direct-imports", "consumer-actual-imports")
    graphs = [e.json("verification/" + label + "-bindings.json") for label in labels]
    indexes = [graph_index(graph, e.raw("verification/" + label + ".log"), label)
               for label, graph in zip(labels, graphs)]
    before_modules, before_parts = indexes[0]
    after_modules, after_parts = indexes[1]
    compare_graphs(before_modules, before_parts, after_modules, after_parts)
    before_projects = {name for name in before_modules if name.startswith("ImbalancedChen.")}
    after_projects = {name for name in after_modules if name.startswith("ImbalancedChen.")}
    require(len(before_projects) == 72 and len(after_projects) == 73,
            "project_module_count_mismatch", "expected 72 inputs and one target")
    selection = e.json("verification/SELECTED_PROJECT_SOURCE_OBJECTS.json")
    require(set(selection.get("expected72_input_module_names", [])) == before_projects
            and set(selection.get("objects", {})) == before_projects
            and set(selection.get("sources", {})) == after_projects,
            "selected_project_set_mismatch", "source/object selection")
    for module in before_projects:
        require(selection["objects"][module] == before_parts[(module, ".olean")]["identity"],
                "selected_project_object_mismatch", module)
    require(selection["sources"][MODULE] == outputs["files"][".lean"], "target_selected_source_mismatch", MODULE)
    target = after_parts[(MODULE, ".olean")]
    require(target["identity"] == outputs["files"][".olean"]
            and target["authority"] == "current_normal_output"
            and target["provider"] == {"source_sha256": SOURCE_SHA256}, "target_import_olean_mismatch", MODULE)
    source_imports = re.findall(r"^import\s+(\S+)", e.raw("project/" + MODULE.replace(".", "/") + ".lean").decode(), re.M)
    require([name for name in after_modules[MODULE]["direct_imports"] if name != "Init"] == source_imports,
            "target_source_compiled_imports_mismatch", MODULE)
    saved = e.json("verification/BEFORE_AFTER_EXACT_OLD_PART_IDENTITY_CHECK.json")
    require(saved.get("old_part_count") == len(before_parts)
            and saved.get("every_selected_old_identity_unchanged") is True
            and saved.get("qualified_original_bytes_preserved") is True
            and saved.get("only_added_part") == [MODULE, ".olean"]
            and saved.get("pre_sha256") == e.members[e.name("verification/" + labels[0] + "-bindings.json")]["sha256"]
            and saved.get("post_sha256") == e.members[e.name("verification/" + labels[1] + "-bindings.json")]["sha256"],
            "saved_graph_comparison_mismatch", "recomputed before/after identities")
    require(summary.get("actual_input_modules") == len(after_modules)
            and summary.get("actual_input_parts") == len(after_parts), "summary_import_count_mismatch", MODULE)
    return {"pre_modules": len(before_modules), "post_modules": len(after_modules),
            "unchanged_old_parts": len(before_parts), "post_parts": len(after_parts),
            "only_added_part": [MODULE, ".olean"], "raw_import_logs_equal_bindings": True,
            "qualified_original_bytes_preserved": True, "pre_post_current_stat_equal_where_present": True,
            "relocations": verify_relocations(e, before_parts, summary),
            "same_path_revalidations": verify_stat_revalidations(e, before_parts)}


def json_lines(raw: bytes, label: str) -> list:
    return [strict_json(line, label) for line in raw.splitlines() if line.strip()]


def guard_slice(raw: bytes, process: dict) -> list:
    start, end = process.get("guard_log_start"), process.get("guard_log_end")
    require(type(start) is int and type(end) is int and 0 <= start <= end <= len(raw),
            "guard_offset_range", process.get("stage", "unknown"))
    require((start == 0 or raw[start - 1:start] == b"\n")
            and (end == 0 or raw[end - 1:end] == b"\n"),
            "guard_offset_line_boundary", process.get("stage", "unknown"))
    rows = json_lines(raw[start:end], "guard slice")
    require(rows == process.get("guarded_commands"), "guard_slice_records_mismatch", process.get("stage", "unknown"))
    return rows


def timestamp(value, label: str) -> datetime:
    require(isinstance(value, str), "timestamp_schema", label)
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    require(parsed.tzinfo is not None and parsed.utcoffset().total_seconds() == 0,
            "timestamp_not_utc", label)
    return parsed


def verify_process(e: Evidence, label: str, command: list, base: str, raw_guard: bytes,
                   stdin_sha256: str | None = None) -> dict:
    process = e.json("verification/" + label + "-process.json")
    invocation = e.json("verification/" + label + "-invocation.json")
    require(isinstance(process, dict) and process.get("stage") == label
            and type(process.get("exit_code")) is int and process["exit_code"] == 0
            and process.get("command") == command and process.get("cwd") == base + "/project"
            and process.get("forbidden_source_calls") == [], "process_command_or_status_mismatch", label)
    require(process.get("log_path") == base + "/verification/" + label + ".log",
            "process_log_path_mismatch", label)
    pinned_member(e, "verification/" + label + ".log", process.get("log_sha256"))
    require(process.get("stdin_sha256") == stdin_sha256
            and invocation.get("stdin_sha256") == stdin_sha256
            and invocation.get("command") == command and invocation.get("cwd") == base + "/project",
            "invocation_process_binding_mismatch", label)
    if stdin_sha256 is not None:
        pinned_member(e, "verification/" + label + ".lean", stdin_sha256)
    require(timestamp(invocation.get("started_utc"), label) <= timestamp(process.get("started_utc"), label)
            <= timestamp(process.get("finished_utc"), label), "stage_time_order", label)
    guard_slice(raw_guard, process)
    return process


def verify_static_guard(e: Evidence, state: dict, base: str) -> None:
    shadow = base + "/runtime/p0-ci-shadow-toolchain"
    state_path = base + "/verification/runtime-evidence/state.json"
    environment = {"LEAN_SYSROOT": shadow, "LAKE_OVERRIDE_LEAN": "true",
                   "LEAN_NUM_THREADS": "2", "ELAN_TOOLCHAIN": PIN, "P0_CI_GUARD_STATE": state_path}
    tools = ["lean", "leanir", "clang", "leanc", "llvm-ar"]
    require(state.get("schema") == "p0-ci-runtime-v1" and state.get("root") == base + "/project"
            and state.get("shadow") == shadow and state.get("realbin") == REALBIN
            and state.get("environment") == environment and state.get("tools") == tools
            and state.get("slot") == base + "/verification/runtime-evidence/compiler.lock"
            and state.get("log") == base + "/verification/runtime-evidence/compiler-commands.jsonl"
            and state.get("guard_sha256") == TOOLS["ci_runtime_guard.py"] and state.get("policy") == POLICY,
            "runtime_state_policy_mismatch", "original guard paths/environment/policy")
    # Static literal and source extraction only. Never eval/import/exec archived code.
    raw = e.raw("original-tools/ci_runtime_guard.py").decode("utf-8")
    tree = ast.parse(raw)
    values = {node.targets[0].id: node.value for node in tree.body
              if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)}
    template = ast.literal_eval(values["WRAPPER"])
    normalizer = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "normalize_lean_args")
    config = {"environment": environment, "shadow": shadow, "realbin": REALBIN,
              "slot": state["slot"], "log": state["log"], "tools": tools}
    expected = template.replace("__CONFIG__", repr(config)).replace(
        "__NORMALIZER__", ast.get_source_segment(raw, normalizer) + "\n").encode()
    runtime = state.get("runtime_sha256")
    require(isinstance(runtime, dict) and all(isinstance(value, str) and SHA256_RE.fullmatch(value)
                                            for value in runtime.values()), "runtime_hash_schema", "runtime_sha256")
    for name in tools:
        member = "verification/runtime-evidence/" + name + "-wrapper.py"
        require(e.raw(member) == expected and runtime.get(shadow + "/bin/" + name) == digest(expected),
                "guard_wrapper_binding_mismatch", name)
    for name, alias in (("lean", "lean-runtime"), ("lake", "lake"), ("leantar", "leantar")):
        require(isinstance(runtime.get(REALBIN + "/" + name), str)
                and runtime[REALBIN + "/" + name] == runtime.get(shadow + "/bin/" + alias),
                "runtime_copy_identity_mismatch", name)
    for name in (*tools, "lake", "leanchecker", "leantar"):
        require(REALBIN + "/" + name in runtime, "runtime_binary_hash_missing", name)
    inputs = state.get("input_sha256")
    require(isinstance(inputs, dict) and set(inputs) == {base + "/" + name for name in CONFIG_MEMBERS},
            "runtime_input_set_mismatch", "project configuration")
    for name in CONFIG_MEMBERS:
        pinned_member(e, name, inputs[base + "/" + name])
    require(e.raw("project/lean-toolchain").decode().strip() == PIN, "toolchain_pin_mismatch", PIN)
    action = ast.literal_eval(values["ACTION_SHA256"])
    require(state.get("action_commit") == ast.literal_eval(values["ACTION_COMMIT"])
            and state.get("action_script_sha256") == {OLD_BASE + "/lean-action/scripts/" + key: value
                                                      for key, value in action.items()},
            "action_script_pin_mismatch", "original lean-action scripts")


def expected_guard_args(arguments: list) -> list:
    """Normalize only the already-whitelisted exact command shapes used here."""
    result = ["-t0", "-j2", "-M12288"]
    for argument in arguments:
        result.extend(["-D", argument[2:]] if argument.startswith("-D") and len(argument) > 2 else [argument])
    return result


def verify_runtime_audit_log(e: Evidence, stage: str, process: dict, raw_guard: bytes, source_count: int) -> dict:
    rows = json_lines(e.raw("verification/" + stage + ".log"), stage)
    diagnostics = [row.get("pinned_sysroot_probe") for row in rows if isinstance(row, dict) and "pinned_sysroot_probe" in row]
    reports = [row for row in rows if isinstance(row, dict) and row.get("status") == "PASS_RUNTIME_GUARD_ONLY"]
    require(len(rows) == 2 and len(diagnostics) == len(reports) == 1
            and set(diagnostics[0]) == {"prefix_matches_shadow", "real_leantar_exists", "real_leantar_within_pin_root",
                                        "shadow_leantar_exists", "shadow_leantar_is_real_symlink", "leantar_hashes_match"}
            and all(value is True for value in diagnostics[0].values()),
            "runtime_probe_log_mismatch", stage)
    end = process["guard_log_end"]
    report = reports[0]
    require(report.get("compiler_commands") == len(json_lines(raw_guard[:end], "guard prefix"))
            and report.get("source_commands") == source_count and report.get("probe") is True
            and report.get("command_log_sha256") == digest(raw_guard[:end])
            and report.get("state_sha256") == e.members[e.name("verification/runtime-evidence/state.json")]["sha256"],
            "runtime_audit_report_binding_mismatch", stage)
    return report


def verify_guard_and_processes(e: Evidence, base: str, summary: dict) -> dict:
    state = e.json("verification/runtime-evidence/state.json")
    verify_static_guard(e, state, base)
    raw_guard = e.raw("verification/runtime-evidence/compiler-commands.jsonl")
    require(raw_guard.endswith(b"\n"), "guard_log_incomplete_line", "compiler-commands.jsonl")
    guard_rows = json_lines(raw_guard, "compiler-commands.jsonl")
    binding = e.json("verification/SEARCH_AND_RUNTIME_BINDING.json")
    paths = binding.get("LEAN_PATH")
    require(isinstance(paths, list) and paths and all(isinstance(path, str) and PurePosixPath(path).is_absolute() for path in paths)
            and paths[0] == base + "/project/.lake/build/lib/lean"
            and OLD_BASE + "/project/.lake/build/lib/lean" not in paths,
            "search_path_binding_mismatch", "independent project first")
    state_path = base + "/verification/runtime-evidence/state.json"
    runner = ["python3", OLD_BASE + "/original-tools/run_guarded.py", "--state", state_path]
    view = runner + ["lake", "env", "env", "LEAN_PATH=" + ":".join(paths)]
    audit = runner + ["python3", OLD_BASE + "/original-tools/ci_runtime_guard.py", "audit", "--state", state_path, "--probe"]
    normal_args = ["-DwarningAsError=true", "-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000",
                   "-o", base + "/project/.lake/build/lib/lean/" + MODULE.replace(".", "/") + ".olean",
                   "-i", base + "/project/.lake/build/lib/lean/" + MODULE.replace(".", "/") + ".ilean",
                   base + "/project/" + MODULE.replace(".", "/") + ".lean"]
    probe_args = ["-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", "--stdin"]
    owned_args = ["-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", "-Dpp.maxSteps=1000000", "--stdin"]
    expected = {
        "runtime-initial-audit": (audit, None), "runtime-final-audit": (audit + ["--require-source"], None),
        "normal-build": (view + ["lean"] + normal_args, None),
        "named-kernel": (view + ["leanchecker", "--verbose", MODULE], None),
        "full-owned": (view + ["lean"] + owned_args, OWNED_DRIVER_SHA256),
        **{label: (view + ["lean"] + probe_args, pin) for label, pin in PROBE_PINS.items()},
    }
    processes = {label: verify_process(e, label, expected[label][0], base, raw_guard,
                                       stdin_sha256=expected[label][1]) for label in STAGES}
    offset, previous_finish = 0, None
    for label in STAGES:
        process = processes[label]
        require(process["guard_log_start"] == offset, "guard_stage_coverage_gap", label)
        if previous_finish is not None:
            require(previous_finish <= timestamp(process["started_utc"], label), "stage_time_overlap", label)
        offset, previous_finish = process["guard_log_end"], timestamp(process["finished_utc"], label)
    require(offset == len(raw_guard), "unclaimed_guard_suffix", str(len(raw_guard) - offset))
    known_inputs = {tuple(normal_args), tuple(probe_args), tuple(owned_args), ("--githash",), ("--print-prefix",), ("--version",)}
    source_calls = []
    for row in guard_rows:
        require(isinstance(row, dict) and type(row.get("pid")) is int and row["pid"] > 0
                and isinstance(row.get("slot_owner"), str) and row["slot_owner"].isdigit()
                and row.get("tool") in state["tools"] and row.get("sysroot") == state["shadow"]
                and isinstance(row.get("input_args"), list) and all(isinstance(arg, str) for arg in row["input_args"])
                and isinstance(row.get("cwd"), str) and PurePosixPath(row["cwd"]).is_absolute(),
                "guard_record_schema", str(row)[:120])
        tool = row["tool"]
        binary = state["shadow"] + "/bin/lean-runtime" if tool == "lean" else state["realbin"] + "/" + tool
        if tool == "lean":
            require(tuple(row["input_args"]) in known_inputs, "unapproved_guard_lean_invocation", str(row["input_args"]))
            require(row.get("command") == [binary] + expected_guard_args(row["input_args"]),
                    "guard_effective_flags_mismatch", str(row["input_args"]))
            if any(argument.endswith(".lean") for argument in row["input_args"]):
                require(row["input_args"] == normal_args and row["cwd"] == base + "/project",
                        "unauthorized_source_invocation", str(row))
                source_calls.append(row)
        else:
            require(row.get("command") == [binary] + row["input_args"], "native_guard_flags_changed", tool)
    require(len(source_calls) == 1 and summary.get("normal_source_invocations") == source_calls,
            "source_invocation_count_mismatch", str(len(source_calls)))
    for label, args in (("normal-build", normal_args), ("nonempty-direct-imports", probe_args),
                        ("consumer-actual-imports", probe_args), ("full-owned", owned_args)):
        require(sum(row.get("tool") == "lean" and row.get("input_args") == args
                    for row in processes[label]["guarded_commands"]) == 1,
                "stage_main_invocation_count_mismatch", label)
    require(sum(row.get("tool") == "lean" and "--stdin" in row["input_args"] for row in guard_rows) == 3,
            "stdin_invocation_count_mismatch", "two import probes and one owned audit")
    for field, stage in (("normal", "normal-build"), ("kernel", "named-kernel"), ("owned", "full-owned"), ("runtime_final", "runtime-final-audit")):
        require(summary.get(field) == processes[stage], "summary_process_mismatch", field)
    replayed = [line.removeprefix("replaying ") for line in e.raw("verification/named-kernel.log").decode().splitlines()
                if line.startswith("replaying ")]
    require(replayed == [MODULE], "named_kernel_target_mismatch", str(replayed))
    setup = e.json("verification/runtime-setup-process.json")
    setup_command = ["python3", OLD_BASE + "/original-tools/ci_runtime_guard.py", "setup", "--evidence", base + "/verification/runtime-evidence"]
    require(setup.get("command") == setup_command and setup.get("cwd") == base + "/project"
            and type(setup.get("exit_code")) is int and setup["exit_code"] == 0
            and setup.get("state_sha256") == e.members[e.name("verification/runtime-evidence/state.json")]["sha256"],
            "runtime_setup_process_mismatch", "setup")
    pinned_member(e, "verification/runtime-setup.log", setup.get("log_sha256"))
    setup_rows = json_lines(e.raw("verification/runtime-setup.log"), "setup")
    require(len(setup_rows) == 2 and all(value is True for value in setup_rows[0].get("pinned_leantar_setup", {}).values())
            and set(setup_rows[0].get("pinned_leantar_setup", {})) == {"real_leantar_exists", "real_leantar_within_pin_root",
                                                                   "shadow_leantar_exists", "shadow_is_real_symlink", "leantar_hashes_match"}
            and setup_rows[1] == {"status": "PREPARED_RUNTIME_GUARD", "state": state_path},
            "runtime_setup_log_mismatch", "setup")
    verify_runtime_audit_log(e, "runtime-initial-audit", processes["runtime-initial-audit"], raw_guard, 0)
    final = verify_runtime_audit_log(e, "runtime-final-audit", processes["runtime-final-audit"], raw_guard, 1)
    require(e.json("verification/runtime-evidence/audit.json") == final,
            "runtime_final_audit_json_mismatch", "final raw log versus audit.json")
    return {"stages_verified": list(STAGES), "stage_exit_codes": {label: 0 for label in STAGES},
            "guard_records": len(guard_rows), "source_invocations": 1, "stdin_audits": 3,
            "original_guard_wrappers_reconstructed_statically": True,
            "guard_log_sha256": digest(raw_guard), "effective_lean_prefix": ["-t0", "-j2", "-M12288"],
            "native_checker_threads_environment": 2}


def verify_evidence(e: Evidence, driver_sha256: str, expected_base: str, package_sha256: str, check_live: bool = False) -> dict:
    run = verify_run(e, driver_sha256, expected_base, package_sha256)
    summary = e.json("verification/VALIDATION_RESULTS.json")
    require(isinstance(summary, dict) and summary.get("schema") == "p29_nonempty_tail_wall_count_validation_v1"
            and summary.get("result") == RESULT and summary.get("module") == MODULE,
            "validation_summary_identity", MODULE)
    require(summary.get("source_sha256") == SOURCE_SHA256 and summary.get("source_git_blob") == SOURCE_GIT_BLOB
            and summary.get("source_bytes") == 6727 and summary.get("normal_warningAsError") is True,
            "validation_summary_source_pin", MODULE)
    require(summary.get("actual_project_inputs") == 72 and summary.get("actual_project_modules_including_target") == 73
            and summary.get("target_normal_invocations") == 1
            and summary.get("supplier_source_kernel_owned_replays") == 0 and summary.get("unknown_input_parts") == 0
            and summary.get("old_qualified_bytes_preserved") is True
            and summary.get("direct_Lean_no_Lake_trace_or_setup_output") is True
            and summary.get("original_guard_runner_owned_parser_unchanged") == TOOLS,
            "validation_summary_scope_mismatch", "one target / existing exact inputs")
    require(summary.get("full_P2_9_complete") is False
            and summary.get("whole_standard_import_kernel_replay_claim") is False,
            "excess_scope_claim", "P2.9 remains open")
    require(e.manifest.get("excludes") == ["FILE_MANIFEST.json"]
            and e.manifest.get("old_supplier_objects_not_duplicated") is True,
            "manifest_scope_mismatch", "single target evidence")
    outputs = verify_source_outputs(e, expected_base, check_live)
    relative = MODULE.replace(".", "/")
    project_members = {"project/" + relative + ".lean", "project/.lake/build/lib/lean/" + relative + ".olean",
                       "project/.lake/build/lib/lean/" + relative + ".ilean"} | CONFIG_MEMBERS
    require({name for name in e.members if name.startswith("project/")} == project_members,
            "unexpected_project_artifacts", "only source, olean, ilean and three configurations")
    owned = verify_owned(e, summary)
    imports = verify_import_graphs(e, summary, outputs)
    runtime = verify_guard_and_processes(e, expected_base, summary)
    return {
        "archive_identity": e.archive_identity, "regular_members_verified": len(e.members),
        "manifest_sha256": e.members[e.manifest_name]["sha256"],
        "manifest_file_identities_verified": len(e.manifest["files"]),
        "driver_sha256": driver_sha256, "run_base": run["base"], "package_relocations_sha256": package_sha256,
        "source_and_outputs": outputs, "owned": owned, "actual_import_bindings": imports,
        "runtime_and_processes": runtime,
        "candidate_increment": {"modules": 1, "owned_declarations": owned["count"]},
        "borrowed_dependencies_added_to_increment": 0,
        "separate_raw_AST_universe_serializer_claim": False,
        "limitations": ["No Lean command rerun and no live rehash of borrowed input objects.",
                        "Historical supplier qualification is retained through pinned run provenance; no new supplier proof replay.",
                        "Service task status, total RSS and CPU allocation require the separate original request/task records.",
                        "Root acceptance and P2.9 closure are separate decisions."],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--archive-bytes", required=True, type=int)
    parser.add_argument("--archive-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--members", required=True, type=int)
    parser.add_argument("--driver-sha256", required=True, help="exact externally reviewed final driver")
    parser.add_argument("--package-relocations-sha256", required=True, help="exact externally reviewed package path document")
    parser.add_argument("--base", required=True, help="expected independent run base")
    parser.add_argument("--output", required=True, type=Path, help="new JSON file; existing files are never overwritten")
    parser.add_argument("--check-live", action="store_true", help="also hash the three target files at their recorded live paths")
    args = parser.parse_args()
    report = {"schema": "p29_nonempty_original_archive_readonly_verification_v1", "archive_path": str(args.archive),
              "target": MODULE, "root_accepted": False, "new_formal_credit": 0,
              "full_P2_9_complete": False, "signed_PP_estimate_complete": False}
    try:
        require(args.archive_bytes > 0 and args.members > 1
                and all(SHA256_RE.fullmatch(value) for value in (args.archive_sha256, args.manifest_sha256, args.driver_sha256,
                                                               args.package_relocations_sha256)),
                "external_pin_schema", "positive archive size/count and lowercase SHA256 values required")
        pins = Pins(args.archive_bytes, args.archive_sha256, args.manifest_sha256, args.members)
        evidence = read_archive(args.archive, pins)
        report.update(verify_evidence(evidence, args.driver_sha256, args.base, args.package_relocations_sha256, args.check_live))
        report["result"] = "PASS_ORIGINAL_NONEMPTY_ARCHIVE_EVIDENCE_CHECKS"
        status = 0
    except (VerificationError, OSError, ValueError, TypeError, KeyError, IndexError, StopIteration, SyntaxError) as error:
        report["result"] = "FAIL"
        report["error"] = {"code": getattr(error, "code", type(error).__name__), "detail": getattr(error, "detail", str(error))}
        status = 1
    report["checked_at_utc"] = datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")
    try:
        with args.output.open("x", encoding="utf-8") as stream:
            json.dump(report, stream, ensure_ascii=False, sort_keys=True, indent=2)
            stream.write("\n")
    except OSError as error:
        print(f"cannot write new output: {error}", file=sys.stderr)
        return 2
    print(json.dumps({"result": report["result"], "output": str(args.output),
                      **({"candidate_increment": report["candidate_increment"]} if status == 0 else {})}, sort_keys=True))
    return status


if __name__ == "__main__":
    raise SystemExit(main())
