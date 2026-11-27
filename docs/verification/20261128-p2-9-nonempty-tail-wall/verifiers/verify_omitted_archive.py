#!/usr/bin/env python3
"""Read-only validation of the pinned OmittedPrimeWall evidence archive.

No extraction, Lean execution, network access, or changes to original evidence.
The only write is a new --output JSON file. A PASS is evidence validation, not
root acceptance, new formal credit, or completion of P2.9.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile


MODULE = "ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall"
SOURCE_SHA256 = "559c7c09e8b38e69f4b076ea8371a48a55b7611ca51482c62686c18db2ef5353"
SOURCE_GIT_BLOB = "8b64194e1381c1dedb59b8d13c715aad0dd94e94"
ALLOWED_AXIOMS = frozenset({"Classical.choice", "Quot.sound", "propext"})
OWNED_DRIVER_SHA256 = "eecdc55119f1334060fa62268454c0eb9d89fb3658be99e8e03ebcc212a43a04"
RESULT = "PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED"
ARCHIVE_DEFAULT = "/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77/qualified-omitted-prime-wall.tar.xz"
MANIFEST_SCHEMA = "p29_omitted_complete_original_single_target_evidence_v1"
CHUNK = 1024 * 1024
CAPTURE_LIMIT = 64 * 1024 * 1024
TOTAL_CAPTURE_LIMIT = 192 * 1024 * 1024
SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
CAPTURE_NAMES = frozenset({
    "FILE_MANIFEST.json", "verification/VALIDATION_RESULTS.json",
    "verification/normal-build-process.json", "verification/normal-build.log",
    "verification/named-kernel-process.json", "verification/named-kernel.log",
    "verification/full-owned-process.json", "verification/full-owned.log", "verification/full-owned.lean",
    "verification/full-owned-DECLARATION_TYPES_AXIOMS.json",
    "verification/full-owned-INVENTORY_NAME_SET_CHECK.json",
    "verification/SOURCE_AND_OUTPUTS_AFTER.json", "verification/SOURCE_AND_OUTPUTS_AFTER_NORMAL.json",
    "verification/omitted-direct-imports-bindings.json", "verification/consumer-actual-imports-bindings.json",
    "verification/BEFORE_AFTER_EXACT_OLD_PART_IDENTITY_CHECK.json",
    "project/ImbalancedChen/P2FiniteMarkedGamma5OmittedPrimeWall.lean",
})


@dataclass(frozen=True)
class Pins:
    archive_bytes: int = 13529388
    archive_sha256: str = "08f8d568f01d80dd4b4fa490b7fbe0d117265e343ebaef0c9d346579f544d978"
    manifest_sha256: str = "9c6092358690df4615ae8f99f2383e06528f18077b25448c2a724569ac393a02"
    members: int = 374


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


def read_archive(path: Path, pins: Pins = Pins()) -> Evidence:
    identity = hash_file(path)
    require(identity["bytes"] == pins.archive_bytes, "archive_bytes_mismatch", str(identity))
    require(identity["sha256"] == pins.archive_sha256, "archive_sha256_mismatch", str(identity))
    members = {}
    captured = {}
    capture_total = 0
    try:
        with tarfile.open(path, "r|xz") as archive:
            for member in archive:
                name = canonical_member(member.name)
                require(name not in members, "duplicate_tar_member", name)
                require(member.type in (tarfile.REGTYPE, tarfile.AREGTYPE)
                        and not member.issparse() and not member.linkname,
                        "unsafe_member_type", f"{name}: {member.type!r}")
                require(len(members) < pins.members, "extra_tar_member", name)
                keep = name in CAPTURE_NAMES
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


def verify_process(evidence: Evidence, summary: dict, field: str, stage: str) -> dict:
    process = evidence.json(f"verification/{stage}-process.json")
    require(process == summary[field], "process_summary_mismatch", stage)
    require(process.get("stage") == stage and type(process.get("exit_code")) is int
            and process["exit_code"] == 0, "process_failed", stage)
    command = process.get("command")
    require(isinstance(command, list) and bool(command)
            and all(isinstance(arg, str) and arg for arg in command),
            "command_schema", stage)
    log_path = process.get("log_path")
    require(isinstance(log_path, str) and PurePosixPath(log_path).is_absolute()
            and PurePosixPath(log_path).name == f"{stage}.log", "log_path_schema", stage)
    log_name = evidence.name(f"verification/{stage}.log")
    require(evidence.members[log_name]["sha256"] == process.get("log_sha256"),
            "process_log_sha256_mismatch", stage)
    require(process.get("forbidden_source_calls") == [], "forbidden_source_calls", stage)
    if "stdin_sha256" in process:
        source_name = evidence.name(f"verification/{stage}.lean")
        require(evidence.members[source_name]["sha256"] == process["stdin_sha256"],
                "process_stdin_sha256_mismatch", stage)
    require(isinstance(process.get("cwd"), str) and Path(process["cwd"]).is_absolute(),
            "process_cwd_schema", stage)
    return process


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
            and len(names) == len(set(names)) == 13, "raw_inventory_names", "expected 13 unique names")
    require(len(totals) == 1 and type(totals[0]) is int and totals[0] == 13
            and len(declarations) == 13, "raw_total_mismatch", str(totals))
    require(counts == [{"count": 13, "module": MODULE}], "raw_module_count_mismatch", str(counts))
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


def verify_owned(evidence: Evidence, summary: dict) -> dict:
    declarations, inventory, axioms = parse_owned(evidence.raw("verification/full-owned.log"))
    require(declarations == evidence.json("verification/full-owned-DECLARATION_TYPES_AXIOMS.json"),
            "raw_declarations_mismatch", "raw audit versus declaration JSON")
    require(inventory == evidence.json("verification/full-owned-INVENTORY_NAME_SET_CHECK.json")
            and inventory == summary.get("inventory"),
            "raw_inventory_mismatch", "raw audit versus inventories")
    require(axioms == summary.get("observed_axioms") == sorted(ALLOWED_AXIOMS),
            "observed_axioms_mismatch", str(axioms))
    require(digest(evidence.raw("verification/full-owned.lean")) == OWNED_DRIVER_SHA256,
            "owned_driver_sha256_mismatch", "unsafe/axiom rejection driver")
    return {"count": len(declarations), "private_name_count": inventory["private_name_count"],
            "names_sha256": inventory["names_sha256"], "observed_axioms": axioms,
            "raw_records_equal_saved_json": True, "unsafe_axiom_rejection_driver_bound": True}


def verify_source_outputs(evidence: Evidence, check_live: bool) -> dict:
    snapshot = evidence.json("verification/SOURCE_AND_OUTPUTS_AFTER.json")
    require(snapshot == evidence.json("verification/SOURCE_AND_OUTPUTS_AFTER_NORMAL.json"),
            "source_outputs_changed_after_normal", "normal versus final snapshot")
    require(isinstance(snapshot, dict) and len(snapshot) == 3, "source_outputs_schema", "expected 3 files")
    by_extension = {}
    live = {}
    for absolute, record in snapshot.items():
        path = PurePosixPath(absolute)
        require(path.is_absolute() and path.suffix in {".lean", ".olean", ".ilean"}
                and path.name == "P2FiniteMarkedGamma5OmittedPrimeWall" + path.suffix
                and path.suffix not in by_extension, "source_output_path_schema", absolute)
        name = evidence.name(path.name)
        require(evidence.members[name] == record, "source_output_archive_identity_mismatch", name)
        by_extension[path.suffix] = {"archive_member": name, "original_path": absolute, **record}
        if check_live:
            require(hash_file(Path(absolute)) == record, "source_output_live_identity_mismatch", absolute)
            live[path.suffix] = record
    require(set(by_extension) == {".lean", ".olean", ".ilean"}, "source_output_extensions", str(by_extension))
    source = evidence.captured[by_extension[".lean"]["archive_member"]]
    blob = hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()
    require(len(source) == 7894 and digest(source) == SOURCE_SHA256 and blob == SOURCE_GIT_BLOB,
            "target_source_identity_mismatch", blob)
    return {"files": by_extension, "source_git_blob": blob,
            "live_check": "PASS_THREE_TARGET_FILES" if check_live else "NOT_REQUESTED"}


def graph_index(graph: dict, modules_expected: int, parts_expected: int) -> tuple[dict, dict]:
    require(isinstance(graph, dict) and graph.get("schema") == "p29_unit_tail_actual_input_parts_v1",
            "import_graph_schema", "unexpected binding schema")
    modules = graph.get("actual_modules")
    parts = graph.get("parts")
    require(isinstance(modules, list) and len(modules) == modules_expected
            and graph.get("module_count") == modules_expected, "import_module_count", str(modules_expected))
    require(isinstance(parts, list) and len(parts) == parts_expected
            and graph.get("part_count") == parts_expected, "import_part_count", str(parts_expected))
    by_module = {}
    for row in modules:
        require(isinstance(row, dict) and isinstance(row.get("module"), str), "import_module_schema", str(row)[:120])
        name = row["module"]
        require(name not in by_module, "duplicate_import_module", name)
        require(type(row.get("is_module")) is bool
                and isinstance(row.get("direct_imports"), list)
                and all(isinstance(x, str) for x in row["direct_imports"])
                and isinstance(row.get("parts"), list), "import_module_schema", name)
        by_module[name] = row
    by_part = {}
    module_part_paths = {name: set() for name in by_module}
    for row in parts:
        require(isinstance(row, dict) and isinstance(row.get("module"), str)
                and isinstance(row.get("facet"), str), "import_part_schema", str(row)[:120])
        key = (row["module"], row["facet"])
        identity = row.get("identity")
        require(key not in by_part and key[0] in by_module, "duplicate_or_unknown_import_part", str(key))
        require(isinstance(identity, dict) and isinstance(identity.get("path"), str)
                and PurePosixPath(identity["path"]).is_absolute()
                and type(identity.get("bytes")) is int and identity["bytes"] >= 0
                and isinstance(identity.get("sha256"), str)
                and SHA256_RE.fullmatch(identity["sha256"]) is not None
                and isinstance(row.get("requested_path"), str)
                and PurePosixPath(row["requested_path"]).is_absolute(), "import_identity_schema", str(key))
        expected_suffix = key[0].replace(".", "/") + key[1]
        require(row["requested_path"].endswith("/" + expected_suffix), "import_facet_path_mismatch", str(key))
        by_part[key] = row
        module_part_paths[key[0]].add((row["requested_path"], identity["path"]))
    for name, module in by_module.items():
        observed = module_part_paths[name]
        declared = module["parts"]
        require(all(isinstance(p, dict) and isinstance(p.get("path"), str)
                    and isinstance(p.get("resolved_path"), str) for p in declared),
                "module_part_path_schema", name)
        require(len(observed) == len(declared)
                and observed == {(p["path"], p["resolved_path"]) for p in declared},
                "module_part_identity_set_mismatch", name)
    return by_module, by_part


def verify_import_graphs(evidence: Evidence, summary: dict, source_outputs: dict) -> dict:
    before_name = evidence.name("verification/omitted-direct-imports-bindings.json")
    after_name = evidence.name("verification/consumer-actual-imports-bindings.json")
    require(evidence.members[before_name]["sha256"] == summary.get("pre_normal_import_bindings_sha256")
            and evidence.members[after_name]["sha256"] == summary.get("actual_input_bindings_sha256"),
            "summary_import_graph_hash_mismatch", "pre/post bindings")
    before_modules, before_parts = graph_index(evidence.json(before_name), 6342, 31074)
    after_modules, after_parts = graph_index(evidence.json(after_name), 6343, 31075)
    require(set(after_modules) - set(before_modules) == {MODULE}
            and set(before_modules) <= set(after_modules), "import_module_delta_mismatch", "expected one target")
    for name in sorted(before_modules):
        require(before_modules[name] == after_modules[name], "old_module_graph_changed", name)
    require(set(after_parts) - set(before_parts) == {(MODULE, ".olean")}
            and set(before_parts) <= set(after_parts), "import_part_delta_mismatch", "expected target .olean")
    for key in sorted(before_parts):
        old, new = before_parts[key], after_parts[key]
        require(all(old.get(field) == new.get(field)
                    for field in ("identity", "requested_path", "authority", "provider")),
                "old_import_part_identity_changed", str(key))
    target_part = after_parts[(MODULE, ".olean")]["identity"]
    target_olean = source_outputs["files"][".olean"]
    require(all(target_part[field] == target_olean[field] for field in ("bytes", "sha256"))
            and target_part["path"] == target_olean["original_path"],
            "target_import_olean_mismatch", MODULE)
    old_check = evidence.json("BEFORE_AFTER_EXACT_OLD_PART_IDENTITY_CHECK.json")
    require(old_check.get("old_part_count") == 31074
            and old_check.get("pre_normal_graph_sha256") == evidence.members[before_name]["sha256"]
            and old_check.get("post_normal_graph_sha256") == evidence.members[after_name]["sha256"]
            and old_check.get("every_old_module_facet_path_bytes_sha256_identical") is True
            and old_check.get("only_added_part") == [MODULE, ".olean"],
            "saved_old_identity_check_mismatch", "recomputed old-part check")
    return {"pre_modules": 6342, "post_modules": 6343, "unchanged_old_parts": 31074,
            "post_parts": 31075, "only_added_part": [MODULE, ".olean"],
            "all_old_module_records_equal": True, "old_live_objects_rehashed": False}


def verify_evidence(evidence: Evidence, check_live: bool = False) -> dict:
    summary = evidence.json("verification/VALIDATION_RESULTS.json")
    require(isinstance(summary, dict)
            and summary.get("schema") == "p29_omitted_prime_wall_P2_normal_named_kernel_full_owned_v1"
            and summary.get("result") == RESULT and summary.get("module") == MODULE,
            "validation_summary_identity", MODULE)
    require(summary.get("source_git_blob") == SOURCE_GIT_BLOB
            and summary.get("source_sha256") == SOURCE_SHA256
            and summary.get("source_bytes") == 7894 and summary.get("owned_count") == 13,
            "validation_summary_source_count", MODULE)
    processes = {field: verify_process(evidence, summary, field, stage)
                 for field, stage in (("normal", "normal-build"), ("kernel", "named-kernel"), ("owned", "full-owned"))}
    normal, kernel, owned = (processes[key] for key in ("normal", "kernel", "owned"))
    require("-DwarningAsError=true" in normal["command"] and summary.get("normal_warningAsError") is True
            and normal["command"][-1].endswith("/ImbalancedChen/P2FiniteMarkedGamma5OmittedPrimeWall.lean"),
            "normal_command_target_mismatch", "warningAsError / target")
    require(kernel["command"][-3:] == ["leanchecker", "--verbose", MODULE]
            and evidence.raw("verification/named-kernel.log").decode().strip() == "replaying " + MODULE,
            "named_kernel_target_mismatch", MODULE)
    require(owned["command"][-1] == "--stdin" and owned.get("stdin_sha256") == OWNED_DRIVER_SHA256,
            "owned_command_binding_mismatch", MODULE)
    source_outputs = verify_source_outputs(evidence, check_live)
    owned_result = verify_owned(evidence, summary)
    imports = verify_import_graphs(evidence, summary, source_outputs)
    require(summary.get("actual_input_modules") == 6343 and summary.get("actual_input_parts") == 31075
            and summary.get("existing_accepted_byte_parts_used") == 31074,
            "summary_import_count_mismatch", "6343 modules / 31075 parts")
    for key in ("borrowed_source_recompilations", "borrowed_new_kernel_replays", "borrowed_new_owned_replays", "reused_successful_v5_stage_reinvocations"):
        require(type(summary.get(key)) is int and summary[key] == 0, "borrowed_replay_claim", key)
    require(summary.get("full_P2_9_complete") is False
            and summary.get("whole_standard_import_kernel_replay_claim") is False,
            "excess_scope_claim", "single target only")
    require(evidence.manifest.get("excludes") == ["FILE_MANIFEST.json"]
            and evidence.manifest.get("borrowed_old_objects_not_duplicated") is True
            and evidence.manifest.get("all_source_kernel_owned_supplier_replays") == 0,
            "manifest_scope_mismatch", "single target original evidence")
    return {
        "archive_identity": evidence.archive_identity,
        "regular_members_verified": len(evidence.members),
        "manifest_member": evidence.manifest_name,
        "manifest_sha256": evidence.members[evidence.manifest_name]["sha256"],
        "manifest_file_identities_verified": len(evidence.manifest["files"]),
        "stage_exit_codes": {field: process["exit_code"] for field, process in processes.items()},
        "source_and_outputs": source_outputs, "owned": owned_result, "actual_import_bindings": imports,
        "candidate_increment": {"modules": 1, "owned_declarations": 13},
        "borrowed_dependencies_added_to_increment": 0,
        "limitations": ["No Lean command rerun; original process/log/driver bindings checked.",
                        "No independent replay of the runtime guard or historical supplier certificates.",
                        "No rehash of the 31074 borrowed live objects.",
                        "Root acceptance and P2.9 closure are separate decisions."],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=Path(ARCHIVE_DEFAULT))
    parser.add_argument("--output", type=Path, required=True,
                        help="new JSON file; existing files are never overwritten")
    parser.add_argument("--check-live", action="store_true",
                        help="add read-only checks of the target source/olean/ilean paths")
    args = parser.parse_args()
    report = {
        "schema": "p29_omitted_original_archive_readonly_verification_v1",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
        "archive_path": str(args.archive),
        "target": MODULE,
        "root_accepted": False,
        "new_formal_credit": 0,
        "full_P2_9_complete": False,
        "signed_PP_estimate_complete": False,
    }
    try:
        evidence = read_archive(args.archive)
        report.update(verify_evidence(evidence, check_live=args.check_live))
        report["result"] = "PASS_ORIGINAL_ARCHIVE_EVIDENCE_CHECKS"
        result_code = 0
    except (VerificationError, OSError, ValueError, TypeError, KeyError) as error:
        report["result"] = "FAIL"
        report["error"] = {"code": getattr(error, "code", type(error).__name__),
                           "detail": getattr(error, "detail", str(error))}
        result_code = 1
    # Deliberately exclusive: neither original evidence nor an earlier report can
    # be overwritten, even if --output is accidentally set to an evidence path.
    try:
        with args.output.open("x", encoding="utf-8") as stream:
            json.dump(report, stream, ensure_ascii=False, sort_keys=True, indent=2)
            stream.write("\n")
    except OSError as error:
        print(f"cannot write new output: {error}", file=sys.stderr)
        return 2
    print(json.dumps({"result": report["result"], "output": str(args.output)}, sort_keys=True))
    return result_code


if __name__ == "__main__":
    raise SystemExit(main())
