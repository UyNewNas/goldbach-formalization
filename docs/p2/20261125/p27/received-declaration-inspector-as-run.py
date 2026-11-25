#!/usr/bin/env python3
"""Inspect this P2.7 delta's original declaration evidence without running Lean.

Usage: python3 -B inspect_actual_declarations.py ACTUAL_DELTA NEW_OUTPUT_DIR

The independent original-export SHA and repository checkpoint are fixed below.
This complements the unchanged p27_delta_evidence.py verify operation; it does
not repeat that operation's scan of the 37 old archive parts. Its reports claim
only receipt/declaration consistency of the actually supplied, anchored bytes.
No report directory is created until every inspection assertion has passed.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib
import json
import lzma
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parent.parent / "goldbach-p27"
CHECKPOINT = "ca15b1035ac8fc9be746fe8108f532f73aaaff2d"
EXPORT_SHA = "73179a250532882aa5a945ba149fb734ee776dd3fdcef5d386af69b6303eca08"
PREFIX = "packages/all.tar.gz/"
ONSITE_ROOT = "/workspace/p2-7-20261125"
COMPLETION = "ImbalancedChen.P2PairedCertificateCompletion"
COMPLETION_NAMESPACE = "ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedCertificateCompletion."
COMPLETION_SUFFIXES = (
    "endpoint_strict_margin", "integral_strict_lower", "actual_grid_strict_lower",
    "support_union_strict_lower", "actual_buchstab_gain_strict_lower",
    "actual_buchstab_difference_strict_lower", "complete_analytic_certificate",
)
BRIDGE = "ImbalancedChen.CurrentPairedBuchstabBridge"
MOVED = (
    "ImbalancedChen.Certificates.P2HistoricalFibreBinding.pairedChenQuarterWeight",
    "ImbalancedChen.Certificates.P2HistoricalFibreBinding.pairedSemanticBuchstabGain",
)
HEADERS = {
    "P27_DELTA_MANIFEST.json", "ORIGINAL_EXPORT_MANIFEST.json",
    "P27_AUDIT_TARGETS.txt", "P27_PROJECT_CLOSURE.json",
}
HELPERS = (
    "inspect_winner9_owner_native.py", "run_winner9_private_checks.py",
    "winner9_external_snapshot.py", "run_winner9_private_audit.py",
    "export_winner9_private_evidence.py",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def file_identity(path):
    before = path.stat()
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            "File changed while hashing: " + str(path))
    return {"path": str(path), "sha256": digest, "bytes": after.st_size}


def decode_json(raw):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "Duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique)


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


def safe_name(name):
    require(isinstance(name, str) and name and "\\" not in name and "\0" not in name,
            "Invalid member/path name")
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and path.as_posix() == name,
            "Unsafe or noncanonical member/path: " + name)
    return name


def git_bytes(relative):
    safe_name(relative)
    return subprocess.check_output(["git", "cat-file", "blob", CHECKPOINT + ":" + relative], cwd=REPO)


def load_frozen_helpers():
    identity = {}
    for name in HELPERS:
        path = REPO / "verification/part2" / name
        expected = git_bytes("verification/part2/" + name)
        require(path.read_bytes() == expected, "Local frozen helper differs from checkpoint: " + name)
        identity[name] = {"path": str(path), "sha256": sha(expected), "bytes": len(expected)}
    sys.path.insert(0, str(REPO / "verification/part2"))
    modules = {}
    for filename in HELPERS:
        name = filename[:-3]
        module = importlib.import_module(name)
        require(Path(module.__file__).resolve() == (REPO / "verification/part2" / filename).resolve(),
                "Another module shadows the frozen helper: " + filename)
        modules[name] = module
    return modules, identity


def retain_member(name):
    return (name in HEADERS or name in {
        PREFIX + "PACKAGE_MANIFEST.json", PREFIX + "EXPORT_METADATA.json",
        PREFIX + "context/records.json", PREFIX + "context/selected-compile-records.json",
    } or (name.startswith(PREFIX + "audits/") and name.endswith("/selected-receipt.json"))
        or name.startswith(PREFIX + "worktree/.lake/p2-private/audit/")
        or name.startswith(PREFIX + "tooling/"))


def read_delta(path):
    seen, captured = {}, {}
    with tarfile.open(path, "r|xz") as archive:
        for member in archive:
            name = safe_name(member.name)
            require(member.isfile() and name not in seen, "Non-file or duplicate delta member: " + name)
            stream = archive.extractfile(member)
            require(stream is not None, "Missing regular member stream")
            digest, size, chunks = hashlib.sha256(), 0, []
            keep = retain_member(name)
            while block := stream.read(1024 * 1024):
                size += len(block)
                digest.update(block)
                if keep:
                    chunks.append(block)
            require(size == member.size, "Truncated member: " + name)
            seen[name] = {"sha256": digest.hexdigest(), "bytes": size}
            if keep:
                captured[name] = b"".join(chunks)
    return seen, captured


def check_envelope(seen, captured):
    delta = decode_json(captured["P27_DELTA_MANIFEST.json"])
    require(delta["schema"] == "p27-text-evidence-delta-v1" and delta["proof_credit"] is False,
            "Unexpected delta schema or proof credit")
    classes = [delta[k] for k in ("embedded", "prior_references", "source_references")]
    sets = [set(group) for group in classes]
    require(not (sets[0] & sets[1] or sets[0] & sets[2] or sets[1] & sets[2]), "Delta classes overlap")
    require(set(seen) == sets[0] | {"P27_DELTA_MANIFEST.json"}, "Embedded delta inventory differs")
    for name, row in classes[0].items():
        require(seen[name] == {key: row[key] for key in ("sha256", "bytes")}, "Embedded bytes differ: " + name)
    raw = captured["ORIGINAL_EXPORT_MANIFEST.json"]
    require(sha(raw) == EXPORT_SHA == delta["original_manifest_sha256"], "Independent original export SHA differs")
    manifest = decode_json(raw)
    require(manifest["export_schema"] == 1 and manifest["worktree"] == ONSITE_ROOT
            and manifest["split"] == "all" and manifest["no_olean_objects"] is True,
            "Unexpected original export scope")
    require(manifest["full_p2_complete"] is False and manifest["full_winner9_family_claimed"] is False,
            "Original whole-project boundary changed")
    require(manifest["packages"] == delta["original_packages"] and len(manifest["packages"]) == 1
            and Path(manifest["packages"][0]["path"]).name == "all.tar.gz", "Original package identity differs")
    package = decode_json(captured[PREFIX + "PACKAGE_MANIFEST.json"])
    require(package["package"] == "all.tar.gz" and package["modules"] == manifest["packages"][0]["modules"]
            and package["files"] == manifest["files"], "Original package/export inventories differ")
    expected = {PREFIX + "PACKAGE_MANIFEST.json"}
    for name, row in manifest["files"].items():
        key = PREFIX + safe_name(name)
        expected.add(key)
        matches = [group[key] for group in classes if key in group]
        require(len(matches) == 1 and all(matches[0][field] == value for field, value in row.items()),
                "Original member coverage/binding differs: " + key)
        if key in sets[1]:
            require(name.startswith("context/native/") and matches[0]["archive_id"] == "p2-resume-main",
                    "Prior reference outside native provenance")
        if key in sets[2]:
            require(name.startswith("sources/") and row["role"] == "verified project source",
                    "Repository reference outside verified project sources")
    require(expected == {name for group in sets for name in group if name.startswith("packages/")},
            "Additional/missing original package members")
    require(decode_json(captured[PREFIX + "EXPORT_METADATA.json"])
            == {key: value for key, value in manifest.items() if key not in {"packages", "files"}},
            "EXPORT_METADATA differs from original manifest")
    targets_raw, closure_raw = captured["P27_AUDIT_TARGETS.txt"], captured["P27_PROJECT_CLOSURE.json"]
    require(targets_raw == git_bytes("docs/p2/20261125/p27/audit-targets.txt")
            and closure_raw == git_bytes("docs/p2/20261125/p27/project-closure.json"), "Fixed scope bytes differ")
    targets, closure = targets_raw.decode().splitlines(), decode_json(closure_raw)
    require(len(targets) == len(set(targets)) == 26 and set(manifest["accepted_modules"]) == set(targets)
            and manifest["accepted_module_count"] == delta["accepted_module_count"] == 26,
            "Expected exactly 26 accepted target modules")
    require(len(closure) == len(set(closure)) == 81 and COMPLETION in closure
            and set(manifest["object_manifest"]) == set(closure) and delta["project_context_count"] == 81,
            "Expected the exact 81-module source/object closure")
    require(manifest["owned_declaration_count"] == manifest["unique_owned_declaration_count"]
            == delta["owned_declaration_count"] == 679 and manifest["duplicate_owned_declarations"] == {}
            and manifest["unselected_modules"] == [], "Original declaration totals/selection differ")
    require(set(package["modules"]) == set(targets), "Package target set differs")
    return manifest, targets, closure


def inspect(archive_path):
    helpers, helper_identities = load_frozen_helpers()
    audit = helpers["run_winner9_private_audit"]
    exporter = helpers["export_winner9_private_evidence"]
    checks = helpers["run_winner9_private_checks"]
    original_archive = file_identity(archive_path)
    seen, captured = read_delta(archive_path)
    manifest, targets, closure = check_envelope(seen, captured)

    def member(relative):
        relative = safe_name(relative)
        name = PREFIX + relative
        require(name in captured, "Required audit/registry artifact is not embedded: " + name)
        row = manifest["files"][relative]
        require(seen[name] == {key: row[key] for key in ("sha256", "bytes")}, "Original member bytes differ")
        return captured[name]

    selected = decode_json(member("context/selected-compile-records.json"))
    registry_raw = member("context/records.json")
    registry = decode_json(registry_raw)
    require(sha(registry_raw) == manifest["records_snapshot_sha256"], "Original registry snapshot SHA differs")
    require(set(selected) == set(closure) and selected == {name: registry[name] for name in closure},
            "81 selected records differ from the original complete registry")
    template = git_bytes("verification/part2/winner9_private_audit_template.lean")
    require(member("tooling/winner9_private_audit_template.lean") == template, "Original audit template differs")
    driver_bytes = {}
    for digest in manifest["driver_sources"]:
        require(digest in exporter.DRIVER_FILES, "Unrecognized original audit driver")
        raw = member("tooling/" + exporter.DRIVER_FILES[digest])
        require(sha(raw) == digest, "Original audit driver SHA differs")
        driver_bytes[digest] = raw

    owner_rows, module_rows, source_rows, global_axioms, used_context = {}, {}, {}, Counter(), set()
    completion_rows, completion_types_raw = None, None
    with tempfile.TemporaryDirectory(prefix="p27-declaration-inspection-") as temporary:
        temp = Path(temporary)
        project = temp / "project"
        for name in closure:
            row = manifest["object_manifest"][name]
            relative = name.replace(".", "/") + ".lean"
            require(row["source"] == relative, "Project source path does not match its module")
            raw = git_bytes(relative)
            require(sha(raw) == row["source_sha256"], "Actual project source differs from fixed Git: " + name)
            info = manifest["files"]["sources/" + relative]
            require(info["sha256"] == sha(raw) and info["bytes"] == len(raw)
                    and info["role"] == "verified project source", "Exported project source identity differs")
            path = project / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            source_rows[name] = {"source": relative, "source_sha256": sha(raw), "bytes": len(raw),
                                 "object_sha256": row["object_sha256"]}

        for target in targets:
            meta = manifest["accepted_modules"][target]
            receipt_relative = "audits/" + target + "/selected-receipt.json"
            receipt_raw = member(receipt_relative)
            receipt = decode_json(receipt_raw)
            require(sha(receipt_raw) == meta["receipt_sha256"] and receipt["accepted"] is True
                    and receipt["module"] == target, "Selected receipt identity/acceptance differs")
            for key in ("source_sha256", "object_sha256", "compile_closure_signature"):
                require(receipt[key] == meta[key], "Receipt/export target binding differs: " + key)
            frozen = receipt["input_snapshot"]
            require(receipt["input_sha256"] == checks.json_digest(frozen), "Original input snapshot digest differs")
            require(frozen["driver_sha256"] == meta["driver_sha256"]
                    and frozen["driver_sha256"] in driver_bytes and frozen["template_sha256"] == sha(template),
                    "Original driver/template binding differs")
            require(frozen["toolchain"]["mathlib_commit"] == checks.PIN
                    and frozen["lean_binary_sha256"] == frozen["toolchain"]["lean_binary_sha256"],
                    "Original compiler/Mathlib binding differs")
            nodes = audit.project_nodes(project, target)
            require(set(nodes) == set(frozen["project"]) == set(meta["project_modules"]), "Original project context differs")
            used_context.update(nodes)
            for name in nodes:
                actual = manifest["object_manifest"][name]
                require(frozen["project"][name] == actual, "Conflicting audited source/object context: " + name)
            # This unchanged function checks recorded closure identities against
            # fixed Git source imports; it does not read/replay onsite objects.
            audit.verify_compilation(selected, nodes, frozen)
            require(receipt["compile_closure_signature"] == selected[target]["closure_signature"]
                    and receipt["source_sha256"] == source_rows[target]["source_sha256"]
                    and receipt["object_sha256"] == source_rows[target]["object_sha256"],
                    "Accepted target differs from its compiled closure")
            require(receipt["replay_binding"] == audit.replay_context(frozen), "Original replay context differs")
            if "external_snapshot" in frozen:
                binding = frozen["external_snapshot"]
                require(frozen["driver_sha256"] not in {exporter.DRIVER_V1, exporter.DRIVER_V2}
                        and meta["external_snapshot"] == binding
                        and manifest["external_snapshots"][checks.json_digest(binding)]["binding"] == binding,
                        "Original external snapshot reference differs")
            replay, owned = receipt["replay"], receipt["audit"]
            require(replay["exit_code"] == 0 and replay["inputs_unchanged"] is True
                    and replay["command"] == [audit.LEANCHECKER, "--verbose", target], "Incomplete original replay")
            require(owned["exit_code"] == 0 and owned["inputs_unchanged"] is True, "Incomplete original owned audit")
            memory = owned.get("memory_mb", 6144)
            require(type(memory) is int and memory in (6144, 11264)
                    and (frozen["driver_sha256"] == exporter.DRIVER_V4 or memory == 6144), "Unexpected audit memory flag")
            require(owned["command"] == [checks.LEAN, "-t0", "-j1", f"-M{memory}", "-DwarningAsError=true",
                                         "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", owned["source"]],
                    "Unexpected original audit command")
            source_path = safe_name(owned["source"])
            require(source_path.startswith(".lake/p2-private/audit/" + target + "/"), "Audit source belongs to another directory")
            parent = str(PurePosixPath(source_path).parent)
            declarations_path, types_path = parent + "/declarations.json", parent + "/types.txt"
            required = {source_path, safe_name(owned["log"]), safe_name(replay["log"]), declarations_path, types_path}
            require(required <= set(receipt["artifacts"]), "Missing accepted artifact bindings")
            artifact_members = {}
            for relative, digest in receipt["artifacts"].items():
                key = PREFIX + "worktree/" + safe_name(relative)
                require(key in seen and seen[key]["sha256"] == digest, "Accepted original artifact SHA differs: " + relative)
                require(manifest["files"]["worktree/" + relative]["sha256"] == digest, "Artifact/export binding differs")
                artifact_members[relative] = {"member": key, **seen[key]}
            require(set(meta["artifact_paths"]) == {receipt_relative} | {
                "worktree/" + relative for relative in receipt["artifacts"]}, "Accepted artifact member list differs")
            actual_template = member("worktree/" + source_path)
            require(actual_template == template.decode().replace(audit.TEMPLATE_TARGET, target).encode()
                    and sha(actual_template) == owned["source_sha256"], "Audit source is not the exact original target template")
            audit_raw = member("worktree/" + owned["log"])
            replay_raw = member("worktree/" + replay["log"])
            require(sha(audit_raw) == owned["log_sha256"] and sha(replay_raw) == replay["log_sha256"], "Stage log SHA differs")
            parse_path = temp / (target + ".audit.log")
            parse_path.write_bytes(audit_raw)
            parsed = audit.parse_audit(parse_path, target, set(nodes))
            require(decode_json(member("worktree/" + declarations_path)) == parsed, "Stored declarations differ from raw audit log")
            types_raw = ("\n\n".join(row["name"] + "\n" + row["type"] for row in parsed["declarations"]) + "\n").encode()
            require(member("worktree/" + types_path) == types_raw, "Stored complete types differ from raw declaration strings")
            if target == COMPLETION:
                completion_rows, completion_types_raw = parsed["declarations"], types_raw
            for key in ("declaration_count", "axiom_counts"):
                require(owned[key] == parsed[key] == meta[key], "Stored audit totals differ: " + key)
            for declaration in parsed["declarations"]:
                require(declaration["name"] not in owner_rows, "Duplicate declaration owner: " + declaration["name"])
                owner_rows[declaration["name"]] = declaration
                global_axioms.update(declaration["axioms"])
            module_rows[target] = {
                "receipt_member": PREFIX + receipt_relative, "receipt_sha256": sha(receipt_raw),
                "input_sha256": receipt["input_sha256"], "compile_closure_signature": receipt["compile_closure_signature"],
                "source_sha256": receipt["source_sha256"], "object_sha256": receipt["object_sha256"],
                "declaration_count": parsed["declaration_count"], "axiom_counts": parsed["axiom_counts"],
                "inventory": parsed["inventory"], "artifact_members": artifact_members,
                "replay_exit_code": replay["exit_code"], "audit_exit_code": owned["exit_code"],
                "project_modules": sorted(nodes),
            }

    require(used_context == set(closure), "Accepted audits do not cover all 81 project contexts")
    require(len(owner_rows) == sum(row["declaration_count"] for row in module_rows.values()) == 679,
            "Expected exactly 679 unique owned declarations")
    require(dict(sorted(global_axioms.items())) == manifest["transitive_axiom_counts"], "Global per-declaration axiom counts differ")
    wanted = {COMPLETION_NAMESPACE + suffix for suffix in COMPLETION_SUFFIXES}
    completion_names = {name for name, row in owner_rows.items() if row["module"] == COMPLETION}
    require(completion_names == wanted and module_rows[COMPLETION]["declaration_count"] == 7,
            "Completion inventory does not contain exactly the expected seven declarations")
    require(completion_rows is not None and completion_types_raw is not None, "Missing original Completion output")
    require(module_rows[BRIDGE]["declaration_count"] == 6, "Expected all six Bridge-owned declarations, including auxiliaries")
    for name in MOVED:
        require(name in owner_rows and owner_rows[name]["module"] == BRIDGE
                and name in module_rows[BRIDGE]["inventory"]["serialized"]
                and name in module_rows[BRIDGE]["inventory"]["environment"], "Moved definition has another/missing owner: " + name)
    require(file_identity(archive_path) == original_archive, "Delta changed during inspection")
    for name, identity in helper_identities.items():
        require(sha(Path(identity["path"]).read_bytes()) == identity["sha256"], "Frozen parser changed during inspection: " + name)
    completion = {
        "schema": "p27-seven-actual-completion-declarations-v1",
        "status": "ORIGINAL_ACCEPTED_DECLARATION_BYTES_VERIFIED",
        "archive": original_archive, "original_manifest_sha256": EXPORT_SHA,
        "module": COMPLETION, "declaration_count": 7,
        "receipt": module_rows[COMPLETION],
        "declarations": completion_rows,
        "types_file_matches_original_audit_member": True, "types_sha256": sha(completion_types_raw),
        "new_lean_invocations": 0, "new_kernel_replay": False,
    }
    report = {
        "schema": "p27-received-audit-declarations-verification-v1",
        "status": "ANCHORED_ORIGINAL_AUDIT_DECLARATIONS_VERIFIED",
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "inspector_sha256": sha(Path(__file__).read_bytes()), "parser_helpers": helper_identities,
        "archive": original_archive, "original_manifest_sha256": EXPORT_SHA, "source_checkpoint": CHECKPOINT,
        "accepted_module_count": 26, "project_context_count": 81,
        "owned_declaration_count": 679, "unique_owned_declaration_count": 679,
        "duplicate_owned_declarations": {}, "unselected_modules": [],
        "transitive_axiom_counts": dict(sorted(global_axioms.items())),
        "allowed_axioms": sorted(audit.AXIOMS), "source_manifest": source_rows,
        "modules": module_rows, "declarations": [owner_rows[name] for name in sorted(owner_rows)],
        "moved_definitions": {name: {"module": owner_rows[name]["module"], "type": owner_rows[name]["type"],
                                     "axioms": owner_rows[name]["axioms"]} for name in MOVED},
        "completion_names": sorted(wanted),
        "transport_boundary": "This inspection does not repeat the frozen delta verifier's actual prior-archive scan. Require that separate successful transport receipt before final P2.7 acceptance.",
        "object_boundary": "Original onsite source/object/replay acceptance is retained through the independent export anchor. No .olean is loaded or newly replayed locally.",
        "original_full_p2_complete": manifest["full_p2_complete"],
        "new_lean_invocations": 0, "new_kernel_replay": False, "overall_p27_completion_claimed": False,
    }
    return {"audit-declarations-verification.json": json_bytes(report),
            "completion-declarations.json": json_bytes(completion), "types.txt": completion_types_raw}


def publish(out, payloads):
    require(not out.exists() and not out.is_symlink(), "Use a new output directory; existing evidence is never overwritten")
    require(out.parent.is_dir(), "Output parent must already exist")
    staging = Path(tempfile.mkdtemp(prefix=".p27-declarations-", dir=out.parent))
    try:
        for name, raw in payloads.items():
            with (staging / name).open("xb") as stream:
                stream.write(raw)
        require(not out.exists() and not out.is_symlink(), "Output appeared during inspection")
        os.rename(staging, out)
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("delta", type=Path)
    parser.add_argument("output_directory", type=Path)
    args = parser.parse_args()
    try:
        require(args.delta.is_file() and not args.delta.is_symlink(), "Supply the actual received regular delta archive")
        archive = args.delta.resolve(strict=True)
        require(not args.output_directory.is_symlink(), "Output directory is redirected")
        out = args.output_directory.absolute()
        require(out.resolve() == out and not out.exists(), "Use a new nonredirected output directory")
        payloads = inspect(archive)
        publish(out, payloads)
    except (ValueError, KeyError, TypeError, OSError, UnicodeError, tarfile.TarError, lzma.LZMAError,
            subprocess.CalledProcessError) as error:
        parser.exit(2, "P2.7 declaration inspection refused: " + str(error) + "\n")
    print(json.dumps({"status": "DECLARATION_INSPECTION_OUTPUTS_WRITTEN", "output_directory": str(out),
                      "files": {name: {"sha256": sha(raw), "bytes": len(raw)} for name, raw in payloads.items()},
                      "new_lean_invocations": 0, "overall_p27_completion_claimed": False}, sort_keys=True))


if __name__ == "__main__":
    main()
