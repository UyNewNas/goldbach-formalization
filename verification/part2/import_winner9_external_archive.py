#!/usr/bin/env python3
"""Run the original P2.10 validation once, retaining its archive on an explicit volume.

This is a separately pinned storage adapter, not a new proof validator. Run its
published copy from .lake/p210-tools/<adapter-commit>/ inside the fixed W1
proof worktree. Numerical provenance remains at the original 94 source.
The original importer, plan and C/A/E sources remain untouched.
Only the registry replacement commits the installation. Precommit failure
removes only this transaction's creations; postcommit failure preserves them.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile


SOURCE_COMMIT = "94c7c507ab747cf4e05a4f19d8d4507cedfede38"
WORKTREE_COMMIT = "7c6fe1e249ffdbdf9b76b166022fc2236b2c69fb"
RUN_ID = "45611402948"
INDEX_SHA = "687c35f8ef018ad85e7cc68581dcadd98cd0acd22bd22f031dfd95966abfc70e"
PLAN_SHA = "46e739a5a5ddfa3ad6b0dd4697f1bf95bb9cbb21ef84ce1c7f32e2cb33162978"
IMPORTER_SHA = "b90f11e049080eff0ccc2d09e63f2d78ce88825791b5c4efdf6a92dc78be188c"
PINS = {
    "import_winner9_ci_artifacts.py": IMPORTER_SHA,
    "run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
    "p210_resume_plan.json": PLAN_SHA,
}
SCHEMA = "p210-external-archive-binding-v1"
FILENAME = "import_winner9_external_archive.py"
RESERVE_BYTES = 64 * 2**20
LOCAL_COPIES = ("import-receipt.json", "local-records-before.json")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def canonical_directory(path, *, missing=False):
    """Check the root itself too; I.no_destination deliberately stops there."""
    path = Path(path)
    require(path.is_absolute() and path == path.resolve(), "Directory must be canonical: " + str(path))
    for parent in (path, *path.parents):
        require(not parent.is_symlink(), "Symlink directory: " + str(parent))
        require((missing and not parent.exists()) or parent.is_dir(), "Not a directory: " + str(parent))
    return path


def available_bytes(path):
    info = os.statvfs(path)
    return info.f_bavail * info.f_frsize


def verify_proof_source(root):
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
            == WORKTREE_COMMIT, "The proof worktree must remain at the fixed W1 source")
    require(not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                        cwd=root, text=True).strip(), "Tracked proof sources are dirty")


def load_original(root, args):
    canonical_directory(root)
    verify_proof_source(root)
    require(args.commit == SOURCE_COMMIT and args.run_id == RUN_ID and args.index_sha256 == INDEX_SHA,
            "Wrong fixed public proof cohort")
    require(re.fullmatch(r"[0-9a-f]{40}", args.adapter_commit) is not None
            and re.fullmatch(r"[0-9a-f]{64}", args.adapter_sha256) is not None,
            "Invalid independent adapter identity")
    runtime = root / ".lake/p210-tools" / args.adapter_commit / FILENAME
    canonical_directory(runtime.parent)
    require(Path(__file__).absolute() == runtime and runtime.is_file() and not runtime.is_symlink()
            and digest(runtime) == args.adapter_sha256, "Adapter location or published SHA differs")
    directory = canonical_directory(root / "verification/part2")
    for name, expected in PINS.items():
        path = directory / name
        require(path.is_file() and not path.is_symlink() and digest(path) == expected,
                "Original source pin differs: " + name)
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(directory))
    modules = {}
    for name in PINS:
        if not name.endswith(".py"):
            continue
        module = importlib.import_module(name[:-3])
        require(Path(module.__file__).absolute() == directory / name,
                "Original module was loaded from another location: " + name)
        modules[name] = module
    importer = modules["import_winner9_ci_artifacts.py"]
    require(importer.C is modules["run_winner9_private_checks.py"]
            and importer.A is modules["run_winner9_private_audit.py"]
            and importer.E is modules["export_winner9_private_evidence.py"],
            "Importer verification modules differ")
    return importer, {"commit": args.adapter_commit, "sha256": args.adapter_sha256, "path": str(runtime)}


def locations(I, root, incoming, temporary, archive_parent, relative):
    for path in (root, incoming, temporary, archive_parent):
        canonical_directory(path)
    require(relative == I.PRIVATE + f"/ci-imports/{RUN_ID}-1-{INDEX_SHA[:12]}",
            "Unexpected original archive destination")
    internal = root / I.safe_name(relative)
    canonical_directory(internal.parent, missing=True)
    external = archive_parent / Path(relative).name
    for protected in (root, incoming, temporary):
        require(not external.is_relative_to(protected) and not protected.is_relative_to(external),
                "External archive overlaps proof, input or cleanup storage")
    I.no_destination(root, relative)
    I.no_destination(archive_parent, external.name)
    return internal, external


def inventory(I, directory, expected):
    actual = {}
    canonical_directory(directory)
    for path in directory.rglob("*"):
        mode = path.lstat().st_mode
        require(stat.S_ISDIR(mode) or stat.S_ISREG(mode), "Linked or special archive entry: " + str(path))
        if stat.S_ISREG(mode):
            actual[I.safe_name(path.relative_to(directory).as_posix())] = path
    require(set(actual) == set(expected), "Archive file inventory differs")
    for name, item in expected.items():
        path = actual[name]
        require(path.stat().st_size == item["bytes"] and I.C.digest(path) == item["sha256"],
                "Archive bytes differ: " + name)


def capacity(I, root, archive_parent, verified, binding_raw):
    """Account for actual EXDEV copies, new registry/binding bytes and a reserve."""
    groups = {}
    for path in (root, archive_parent):
        device = path.stat().st_dev
        item = groups.setdefault(device, {"paths": [], "available_bytes": available_bytes(path),
                                           "copy_bytes": 0, "new_bytes": 0, "reserve_bytes": RESERVE_BYTES})
        item["paths"].append(str(path))
        item["available_bytes"] = min(item["available_bytes"], available_bytes(path))
    transfers = [(verified["stage"] / name, root) for name in verified["files"]]
    transfers += [(verified["archive"] / name, archive_parent) for name in verified["archive_files"]]
    transfers += [(verified["archive"] / "import-receipt.json", root), (verified["records_path"], root)]
    for source, destination in transfers:
        require(source.is_file() and not source.is_symlink(), "Not a regular transfer source")
        device = destination.stat().st_dev
        if source.stat().st_dev != device:
            groups[device]["copy_bytes"] += source.stat().st_size
    groups[root.stat().st_dev]["new_bytes"] += len(binding_raw) + len(verified["merged_raw"])
    for item in groups.values():
        item["required_bytes"] = item["copy_bytes"] + item["new_bytes"] + item["reserve_bytes"]
        require(item["available_bytes"] >= item["required_bytes"], "Insufficient writable capacity for storage transaction")
    return {str(device): item for device, item in groups.items()}


def install_split_archive(I, root, incoming, temporary, archive_parent, verified, adapter, state):
    """Keep I.validate's return value intact; only separate installation roots."""
    require(not state.get("committed"), "Transaction was already committed")
    verify_proof_source(root)
    internal, external = locations(I, root, incoming, temporary, archive_parent, verified["archive_relative"])
    require(verified["stage"] == temporary / "worktree" and verified["archive"] == temporary / "archive",
            "Unexpected validation staging locations")
    require(verified["records_path"] == root / I.PRIVATE / "records.json", "Changed registry destination")
    runtime = root / ".lake/p210-tools" / adapter["commit"] / FILENAME
    canonical_directory(runtime.parent)
    require(set(adapter) == {"commit", "sha256", "path"} and adapter["path"] == str(runtime),
            "Changed adapter identity")
    adapter_frozen = {runtime: adapter["sha256"]}
    I.unchanged(adapter_frozen)
    I.unchanged(verified["inputs"])
    for name in verified["files"]:
        I.no_destination(root, name)
    old_raw = verified["records_path"].read_bytes()
    old, merged = json.loads(old_raw), json.loads(verified["merged_raw"])
    imported_path = verified["archive"] / "import-receipt.json"
    imported = I.read(imported_path)
    require(I.C.digest(imported_path) == verified["archive_files"]["import-receipt.json"],
            "Original import receipt changed")
    added = set(merged) - set(old)
    require(len(added) == 598 and added == set(imported["modules"])
            and set(merged) == set(old) | added and all(merged[name] == value for name, value in old.items())
            and imported["installed_files"] == verified["files"], "Full old/new registry boundary differs")
    before, after = hashlib.sha256(old_raw).hexdigest(), hashlib.sha256(verified["merged_raw"]).hexdigest()
    require(imported["records_before_sha256"] == before == verified["inputs"][verified["records_path"]]
            and imported["records_after_sha256"] == after
            and (verified["archive"] / "local-records-before.json").read_bytes() == old_raw,
            "Original registry bytes differ")
    require(imported["commit"] == SOURCE_COMMIT and imported["run_id"] == RUN_ID
            and imported["index_sha256"] == INDEX_SHA and imported["terminal_integrated"] is False,
            "Original import receipt provenance differs")
    archive_files = {I.safe_name(name): {"sha256": sha, "bytes": (verified["archive"] / name).stat().st_size}
                     for name, sha in verified["archive_files"].items()}
    binding = {
        "schema": SCHEMA,
        "source": {"commit": SOURCE_COMMIT, "run_id": RUN_ID, "run_attempt": 1,
                   "index_sha256": INDEX_SHA, "plan_sha256": PLAN_SHA, "importer_sha256": IMPORTER_SHA},
        "adapter": dict(adapter),
        "validation": {"calls": 1, "original_install_invoked": False, "version_probe": 1,
                       "proof_compilation": 0, "stock_replay": 0},
        "archive_root": str(external), "archive_relative": verified["archive_relative"],
        "archive_files": archive_files,
        "local_copies": {name: archive_files[name] for name in LOCAL_COPIES},
        "registry": {"before_sha256": before, "after_sha256": after, "before_count": len(old),
                     "added_count": len(added), "after_count": len(merged)},
    }
    binding_raw = I.E.encoded(binding)
    resources = capacity(I, root, archive_parent, verified, binding_raw)
    created_files, created_dirs, pending = [], [], None
    parent_identities = {path: (path.stat().st_dev, path.stat().st_ino) for path in (root, archive_parent)}

    def parents(path):
        missing = []
        while not path.exists():
            require(not path.is_symlink(), "Linked destination parent")
            missing.append(path)
            path = path.parent
        canonical_directory(path)
        for directory in reversed(missing):
            directory.mkdir(mode=0o700)
            created_dirs.append(directory)

    def transfer(source, destination, expected, parent):
        I.no_destination(parent, destination.relative_to(parent).as_posix())
        parents(destination.parent)
        I.exclusive_link_or_copy(source, destination, expected)
        created_files.append(destination)

    try:
        for name, sha in verified["files"].items():
            transfer(verified["stage"] / name, root / name, sha, root)
        I.no_destination(archive_parent, external.name)
        external.mkdir(mode=0o700)
        created_dirs.append(external)
        for name, item in archive_files.items():
            transfer(verified["archive"] / name, external / name, item["sha256"], external)
        I.no_destination(root, verified["archive_relative"])
        parents(internal.parent)
        internal.mkdir(mode=0o700)
        created_dirs.append(internal)
        transfer(verified["records_path"], internal / "local-records-before.json", before, internal)
        transfer(imported_path, internal / "import-receipt.json", archive_files["import-receipt.json"]["sha256"], internal)
        binding_path = internal / "external-archive.json"
        with binding_path.open("xb") as stream:
            created_files.append(binding_path)
            stream.write(binding_raw)
            stream.flush()
            os.fsync(stream.fileno())
        I.unchanged(verified["inputs"])
        require(I.A.snapshot(root, root / I.PRIVATE / "lib", verified["base"], verified["toolchain"])
                == verified["old_snapshot"], "Accepted dependencies changed before registry commit")
        verify_proof_source(root)
        I.unchanged(adapter_frozen)
        for path, identity in parent_identities.items():
            canonical_directory(path)
            require((path.stat().st_dev, path.stat().st_ino) == identity, "Storage parent changed")
        inventory(I, external, archive_files)
        internal_files = dict(binding["local_copies"], **{
            "external-archive.json": {"sha256": hashlib.sha256(binding_raw).hexdigest(), "bytes": len(binding_raw)}})
        inventory(I, internal, internal_files)
        with tempfile.NamedTemporaryFile(prefix=".records-ci-import-", dir=verified["records_path"].parent,
                                         delete=False) as stream:
            pending = Path(stream.name)
            stream.write(verified["merged_raw"])
            stream.flush()
            os.fsync(stream.fileno())
        require(I.C.digest(verified["records_path"]) == before, "Another process changed the registry")
        os.replace(pending, verified["records_path"])
        state["committed"] = True
    finally:
        if not state["committed"]:
            for path in reversed(created_files):
                path.unlink(missing_ok=True)
            for directory in reversed(created_dirs):
                try:
                    directory.rmdir()
                except OSError:
                    pass
        if pending is not None:
            pending.unlink(missing_ok=True)
    return {"status": "P210_EXTERNAL_ARCHIVE_INSTALLED_EXACT", "committed": True,
            "binding": str(binding_path), "binding_sha256": hashlib.sha256(binding_raw).hexdigest(),
            "archive_root": str(external), "registry": binding["registry"], "resources": resources,
            "installed_file_count": len(verified["files"]),
            "installed_files_logical_bytes": sum((root / name).stat().st_size for name in verified["files"]),
            "archive_file_count": len(archive_files),
            "archive_files_logical_bytes": sum(item["bytes"] for item in archive_files.values()),
            "size_accounting": "logical_file_bytes_not_unique_disk_usage",
            "original_validation_calls": 1, "original_install_invoked": False,
            "version_probe": 1, "proof_compilation": 0, "stock_replay": 0}


def receive(I, root, incoming, archive_parent, staging_parent, args, adapter, state, emit):
    with tempfile.TemporaryDirectory(prefix="p210-ci-import-", dir=staging_parent) as directory:
        temporary = Path(directory).resolve()
        state["phase"] = "preflight"
        relative = I.PRIVATE + f"/ci-imports/{RUN_ID}-1-{INDEX_SHA[:12]}"
        locations(I, root, incoming, temporary, archive_parent, relative)
        state["phase"] = "validation"
        verified = I.validate(root, incoming, temporary, args)
        state["phase"] = "installation"
        result = install_split_archive(I, root, incoming, temporary, archive_parent, verified, adapter, state)
    state["phase"] = "report"
    emit(json.dumps(result, sort_keys=True))
    state["phase"] = "complete"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("collection", type=Path)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--index-sha256", required=True)
    parser.add_argument("--archive-parent", type=Path, required=True)
    parser.add_argument("--staging-parent", type=Path)
    parser.add_argument("--adapter-commit", required=True)
    parser.add_argument("--adapter-sha256", required=True)
    args = parser.parse_args()
    state = {"committed": False, "phase": "identity"}
    try:
        root, incoming = Path.cwd().resolve(), args.collection.resolve()
        I, adapter = load_original(root, args)
        archive_parent = canonical_directory(args.archive_parent)
        staging_parent = canonical_directory(args.staging_parent) if args.staging_parent else None
        receive(I, root, incoming, archive_parent, staging_parent, args, adapter, state,
                lambda line: print(line, flush=True))
        return 0
    except BaseException as error:
        # The committed flag, not a later report failure, decides data preservation.
        failure = {"status": "P210_EXTERNAL_ARCHIVE_RECEPTION_INCOMPLETE", **state,
                   "exception_type": type(error).__name__, "error": str(error),
                   "proof_compilation": 0, "stock_replay": 0}
        try:
            print(json.dumps(failure, sort_keys=True), file=sys.stderr, flush=True)
        except OSError:
            pass
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
