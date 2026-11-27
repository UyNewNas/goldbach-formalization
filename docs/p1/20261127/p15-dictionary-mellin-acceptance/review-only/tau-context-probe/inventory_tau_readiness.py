#!/usr/bin/env python3
"""Print a bounded read-only inventory for the original P1 TauTruncation lane."""

import hashlib
import json
import os
from pathlib import Path
import re
import stat


PROJECT = Path("/workspace/blue-member-build")
REPOSITORY = Path("/workspace/goldbach-formalization")
NATIVE_PACKAGE = PROJECT / ".lake/packages/goldbach"
ORIGINAL_ROOT = Path("/workspace/p1-complete-proof/20261126-p15-current-corrections-v1")
TOOLS = Path("/workspace/blue-build-tools")
GUARD = TOOLS / "run_guarded.py"
SERIALIZER = TOOLS / "serialize_validation_lane.py"
STATE = TOOLS / "member-runtime-evidence/state.json"

TARGET = "ImbalancedChen.Part3ElementaryTauTruncation"
NATIVE = "MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean"
SOURCE_PINS = {
    TARGET: {"bytes": 11349, "sha256": "8e315aec5a3f00506ac26e8710474c47a448b043d3cf38be27c4df30c18a478f"},
    NATIVE: {"bytes": 17917, "sha256": "4e119e53ec5df626bb7e02aa44bf950dbe721bd1f2767fba5fbf90c30784ff59"},
}
RUNTIME_PINS = {
    GUARD: {"bytes": 891, "sha256": "c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526"},
    SERIALIZER: {"bytes": 2404, "sha256": "734602546772451e12fcbe8d8c3380ee2db9211db30444cbb524c59c79a8f368"},
    STATE: {"bytes": 4462, "sha256": "9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152"},
}
COMMIT = re.compile(r"[0-9a-f]{40}")
ATTEMPT = re.compile(r"attempt-[0-9]{5}")
AUDIT_PASS = "PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS"
LIB = (".olean", ".olean.hash", ".olean.private", ".olean.private.hash",
       ".olean.server", ".olean.server.hash", ".ilean", ".ilean.hash",
       ".trace", ".trace.nobuild", ".ir", ".ir.hash", ".ir.sig", ".ir.sig.hash")
IR = (".c", ".c.hash", ".setup.json", ".bc", ".bc.hash",
      ".o", ".o.hash", ".o.export", ".o.export.hash")
REQUIRED_NATIVE = (".olean", ".olean.hash", ".ilean", ".ilean.hash",
                   ".trace", ".c", ".c.hash", ".setup.json")


def kind(path):
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        return "absent"
    if stat.S_ISLNK(mode):
        return "symlink"
    if stat.S_ISREG(mode):
        return "regular"
    if stat.S_ISDIR(mode):
        return "directory"
    return "other"


def file_info(path, *, include_json=False):
    state = kind(path)
    info = {"path": str(path), "kind": state}
    if state != "regular":
        return info
    if path.resolve() != path:
        return {**info, "kind": "symlink_ancestor"}
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, "rb") as stream:
        before = os.fstat(stream.fileno())
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
        document = None
        if include_json and before.st_size <= 4 * 1024 * 1024:
            stream.seek(0)
            try:
                document = json.load(stream)
            except (UnicodeError, ValueError):
                pass
        after = os.fstat(stream.fileno())
    if (before.st_size, before.st_mtime_ns, before.st_ino) != (
        after.st_size, after.st_mtime_ns, after.st_ino
    ):
        raise RuntimeError(f"file changed during read: {path}")
    info.update(bytes=before.st_size, sha256=digest)
    if include_json:
        info["json_is_object"] = isinstance(document, dict)
        if isinstance(document, dict):
            info["json_status"] = document.get("status")
            info["json_module"] = document.get("module")
            info["json_source_commit"] = document.get("source_commit")
            info["json_target_source_sha256"] = (
                document["modules"].get(TARGET) if isinstance(document.get("modules"), dict) else None
            )
            info["json_depHash"] = document.get("depHash")
    return info


def pinned_file(path, pin):
    info = file_info(path)
    return {"expected": pin, "observed": info,
            "matches": all(info.get(key) == value for key, value in pin.items())}


def module_inventory(root, module):
    relative = Path(*module.split("."))
    paths = {
        suffix: root / ".lake/build/lib/lean" / (str(relative) + suffix)
        for suffix in LIB
    }
    paths.update({suffix: root / ".lake/build/ir" / (str(relative) + suffix) for suffix in IR})
    return {
        "source": pinned_file(root / relative.with_suffix(".lean"), SOURCE_PINS[module]),
        "artifacts": {
            suffix: file_info(path, include_json=(suffix == ".trace"))
            for suffix, path in sorted(paths.items())
        },
    }


def directories(path, pattern):
    state = kind(path)
    if state == "absent":
        return []
    if state != "directory" or path.resolve() != path:
        raise RuntimeError(f"expected a real evidence directory: {path}")
    return sorted(entry for entry in path.iterdir() if pattern.fullmatch(entry.name))


def owner_history():
    history = []
    for commit in directories(ORIGINAL_ROOT, COMMIT):
        if kind(commit) != "directory":
            raise RuntimeError(f"non-directory commit evidence entry: {commit}")
        owner = commit / TARGET
        owner_kind = kind(owner)
        attempts = [
            {"path": str(attempt / TARGET), "kind": kind(attempt / TARGET)}
            for attempt in directories(commit / "runs", ATTEMPT)
            if kind(attempt) == "directory" and kind(attempt / TARGET) != "absent"
        ]
        if owner_kind == "absent" and not attempts:
            continue
        evidence = {"commit": commit.name, "owner_path": str(owner), "owner_kind": owner_kind,
                    "target_paths_in_attempts": attempts, "classification": "PARTIAL_OR_UNVERIFIED"}
        if owner_kind == "directory":
            normal = file_info(owner / "normal" / TARGET / "NORMAL_PASS.json", include_json=True)
            audits = [
                {
                    "directory": str(audit),
                    "plan": file_info(audit / "AUDIT_PLAN.json"),
                    "receipt": file_info(audit / "lane-0/VALIDATION_RESULTS.json", include_json=True),
                }
                for audit in directories(owner / "audits", re.compile(r"[^.][^/]*"))
                if kind(audit) == "directory"
            ]
            evidence.update(normal=normal, audits=audits)
            if (normal.get("json_status") == "NORMAL_PASS_AUDIT_PENDING"
                    and normal.get("json_module") == TARGET
                    and normal.get("json_source_commit") == commit.name
                    and any(audit["receipt"].get("json_status") == AUDIT_PASS
                            and audit["receipt"].get("json_target_source_sha256") == SOURCE_PINS[TARGET]["sha256"]
                            for audit in audits)):
                evidence["classification"] = "MATCHING_NORMAL_AND_AUDIT_RECEIPTS_FOUND_UNREVALIDATED"
        history.append(evidence)
    return history


def inventory():
    tau = module_inventory(PROJECT, TARGET)
    native = module_inventory(NATIVE_PACKAGE, NATIVE)
    history = owner_history()
    native_missing = [
        suffix for suffix in REQUIRED_NATIVE
        if native["artifacts"][suffix]["kind"] != "regular"
    ]
    runtime = {str(path): pinned_file(path, pin) for path, pin in RUNTIME_PINS.items()}
    stock = ["lake", "--no-build", "build", "+" + NATIVE + ":olean"]
    observations = []
    if native_missing or not native["source"]["matches"]:
        observations.append("NATIVE_SOURCE_OR_ARTIFACT_INVENTORY_INCOMPLETE")
    if not all(row["matches"] for row in runtime.values()):
        observations.append("ORIGINAL_RUNTIME_PIN_NOT_CONFIRMED")
    if kind(ORIGINAL_ROOT) != "directory":
        observations.append("ORIGINAL_OWNER_ROOT_NOT_AVAILABLE")
    if history or any(row["kind"] != "absent" for row in tau["artifacts"].values()):
        observations.append("TARGET_PRIOR_OR_PARTIAL_STATE_OBSERVED")
    return {
        "schema": "p15_tau_truncation_readonly_inventory_v1",
        "status": "READONLY_INVENTORY_COLLECTED",
        "inventory_observations": observations,
        "project": str(PROJECT),
        "target": TARGET,
        "original_owner_root": {"path": str(ORIGINAL_ROOT), "kind": kind(ORIGINAL_ROOT)},
        "owner_history": history,
        "target_project_inventory": tau,
        "target_checkout_source": pinned_file(
            REPOSITORY / Path(*TARGET.split(".")).with_suffix(".lean"), SOURCE_PINS[TARGET]
        ),
        "native_project_inventory": native,
        "native_missing_required_artifacts": native_missing,
        "original_runtime": runtime,
        "stock": {
            "executed": False,
            "planned_argv": stock,
            "planned_guard_argv": ["python3", str(GUARD), "--state", str(STATE), *stock],
            "original_serializer_argv_prefix": [
                "python3", str(SERIALIZER), "--state", str(STATE), "--receipt"
            ],
            "exit_code": None,
            "log": None,
            "actual_built_modules": None,
            "actual_failed_modules": None,
            "tool_semantics_observation": (
                "Pinned Lake can write a .trace.nobuild sidecar on its out-of-date no-build path."
            ),
        },
        "new_owner_accepted": False,
    }


if __name__ == "__main__":
    try:
        print(json.dumps(inventory(), indent=2, sort_keys=True))
    except (OSError, RuntimeError) as error:
        print(json.dumps({"status": "INVENTORY_INCOMPLETE", "error": str(error),
                          "stock_executed": False, "new_owner_accepted": False}, sort_keys=True))
        raise SystemExit(3)
