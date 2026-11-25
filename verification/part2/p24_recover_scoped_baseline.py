#!/usr/bin/env python3
"""Recover duplicate baseline copies after P2.4 ENOSPC; preserve proof gates.

Default: read-only plan on stdout. --apply removes only evidenced, unprotected
duplicates and records the recovery. After the caller refreshes the owned
branch, --prepare-mirror creates an independent same-commit baseline clone with
a scoped object library and records the actual runtime source HEAD.
Supports python3 -B -c '<this complete source>' from the target checkout when
there is no disk space to install this file. The isolated checkout must have
one cooperative writer; the existing migration lock is held throughout.
"""
from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys

sys.dont_write_bytecode = True

BASELINE = "8657cfffef159185f73c6a04ae4d31c846c0d0a9"
OWN_BRANCH = "work/p2-4-compact-proof-20261125"
ROOT = "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"
MIGRATION_STATUS = "EXACT_PREVIOUSLY_VERIFIED_CACHE_TRANSPORT_NOT_NEW_COMPILATION"
LOAD_SUFFIXES = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")
COPY_SUFFIXES = tuple(sorted(set(LOAD_SUFFIXES + tuple(s + ".hash" for s in LOAD_SUFFIXES)
                                 + (".ilean", ".ilean.hash", ".trace", ".ir.setup.json")),
                             key=len, reverse=True))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def identity(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode), "Not a regular file: " + str(path))
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_nlink]


def file_state(path):
    before = identity(path)
    result = {"identity": before, "sha256": digest(path), "bytes": before[2],
              "allocated_bytes": path.stat().st_blocks * 512}
    require(identity(path) == before, "File changed while hashing: " + str(path))
    return result


def safe_path(root, path):
    path = path.absolute()
    require(path.is_relative_to(root), "Path outside owned/read-only root: " + str(path))
    current = root
    require(not root.is_symlink() and root.resolve() == root, "Root must have a stable physical path")
    for part in path.relative_to(root).parts:
        current /= part
        require(not current.is_symlink(), "Symlink in path: " + str(current))
        require(current.resolve().is_relative_to(root), "Physical path escaped its root")


def git(root, *args, raw=False, allow_file=False):
    return subprocess.check_output(["git", "-c", "protocol.allow=never", "-c",
                                    "protocol.file.allow=" + ("always" if allow_file else "never"), *args], cwd=root,
                                   env=dict(os.environ, GIT_OPTIONAL_LOCKS="0", GIT_NO_LAZY_FETCH="1"), text=not raw)


def clean_head(root, expected=None):
    require(Path(git(root, "rev-parse", "--show-toplevel").strip()).resolve() == root,
            "Expected an exact Git checkout root")
    head = git(root, "rev-parse", "HEAD").strip()
    require(expected is None or head == expected, "Unexpected Git commit: " + str(root))
    require(not git(root, "status", "--porcelain", "--untracked-files=no").strip(),
            "Tracked checkout is dirty: " + str(root))
    return head


def graph(project):
    sys.path.insert(0, str(project / "verification/part2"))
    from run_winner9_private_audit import project_nodes
    return project_nodes(project, ROOT)


def write_new(path, value):
    raw = (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def module_of(relative):
    for suffix in COPY_SUFFIXES:
        if relative.endswith(suffix):
            name = relative[:-len(suffix)].replace("/", ".")
            if re.fullmatch(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9]*)+", name):
                return name
    return None


class Recovery:
    def __init__(self, project, baseline, donor, snapshot, attempt="attempt-001"):
        self.project, self.baseline, self.donor = (Path(p).absolute() for p in (project, baseline, donor))
        require(re.fullmatch(r"attempt-[0-9]{3}", attempt), "Use an attempt-NNN directory")
        for root in (self.project, self.baseline, self.donor):
            require(root.resolve(strict=True) == root, "Use a physical checkout path")
        require(not self.project.is_relative_to(self.baseline) and not self.baseline.is_relative_to(self.project)
                and not self.project.is_relative_to(self.donor) and not self.donor.is_relative_to(self.project),
                "Target, original baseline, and donor must be disjoint")
        self.lib = self.project / ".lake/p2-private/lib"
        self.base_lib = self.baseline / ".lake/build/lib/lean"
        self.out = self.project / (".lake/p24-disk-recovery/" + attempt)
        self.mirror_root = self.project / (".lake/p24-baseline-8657/" + attempt)
        self.records_path = self.project / ".lake/p2-private/records.json"
        self.receipt_path = self.project / ".lake/p24-cache-migration/attempt-001/MIGRATION.json"
        self.snapshot = Path(snapshot).resolve(strict=True)
        for path in (self.lib, self.out, self.mirror_root, self.records_path, self.receipt_path):
            safe_path(self.project, path)
        safe_path(self.baseline, self.base_lib)
        require(self.lib.is_dir() and self.base_lib.is_dir(), "Missing existing object library")
        self.source_head = clean_head(self.project)
        require(git(self.project, "branch", "--show-current").strip() == OWN_BRANCH, "Not the owned task branch")
        clean_head(self.baseline, BASELINE)
        self.records_raw, self.receipt_raw = self.records_path.read_bytes(), self.receipt_path.read_bytes()
        self.records, self.receipt = json.loads(self.records_raw), json.loads(self.receipt_raw)
        require(isinstance(self.records, dict), "Registry must be an object")
        self.check_migration()
        self.nodes = graph(self.project)
        self.source_hashes = {str(n["source"]): digest(n["source"]) for n in self.nodes.values()}
        self.protected = set(self.nodes) | set(self.receipt["actual_project_scope"]) | set(self.records)
        self.protected_paths = set()
        registries = sorted((self.project / ".lake/p2-private").glob("*records.json"))
        self.registry_paths = registries
        for path in registries:
            safe_path(self.project, path)
            self.protect_records(json.loads(path.read_bytes()))
        self.input_states = {str(p): file_state(p) for p in (*registries, self.receipt_path, self.snapshot)}
        self.tracked = self.tracked_files()
        self.plan = self.make_plan()

    def protect_records(self, value):
        if isinstance(value, list):
            for row in value:
                self.protect_records(row)
        elif isinstance(value, dict):
            for key, row in value.items():
                if isinstance(key, str) and key.startswith("ImbalancedChen."):
                    self.protected.add(key)
                self.protect_records(row)
            if isinstance(value.get("module"), str):
                self.protected.add(value["module"])
            if isinstance(value.get("object"), str):
                obj = Path(value["object"])
                for referent in (obj if obj.is_absolute() else self.project / obj, self.lib / obj):
                    path = referent.resolve(strict=False)
                    if path.is_relative_to(self.lib):
                        relative = str(path.relative_to(self.lib))
                        self.protected_paths.add(relative)
                        name = module_of(relative)
                        if name is not None:
                            self.protected.add(name)

    def check_migration(self):
        receipt = self.receipt
        require(receipt.get("schema") == "p24-verified-private-cache-transport-v1"
                and receipt.get("status") == MIGRATION_STATUS and receipt.get("root") == ROOT
                and receipt.get("project_root") == str(self.project)
                and receipt.get("donor_root") == str(self.donor), "Migration receipt identity/status mismatch")
        scope = receipt.get("actual_project_scope")
        require(isinstance(scope, list) and ROOT in scope and all(isinstance(n, str) for n in scope),
                "Migration lacks its original project scope")
        migrated = receipt.get("migrated")
        require(isinstance(migrated, dict) and set(migrated) <= set(scope), "Malformed migrated module list")
        binding = {"path": str(self.receipt_path), "sha256": hashlib.sha256(self.receipt_raw).hexdigest()}
        for name in migrated:
            require(self.records.get(name, {}).get("verified_cache_migration") == binding,
                    "Migration receipt was not published in registry: " + name)
        external = receipt.get("new_external_binding", {})
        names = external.get("native_modules", [])
        require(external.get("snapshot") == str(self.snapshot)
                and external.get("snapshot_sha256") == digest(self.snapshot)
                and external.get("lean_path", [None])[0] == str(self.lib)
                and len(names) == len(set(names)) == 515, "Migration external binding differs")

    def tracked_files(self):
        result = {}
        for entry in git(self.baseline, "ls-tree", "-rlz", BASELINE, raw=True).split(b"\0"):
            if not entry:
                continue
            header, name = entry.split(b"\t", 1)
            parts = header.split()
            if parts[1] == b"blob":
                result[name.decode()] = int(parts[-1])
        require(not any(p.startswith(".lake/build/lib/lean/") for p in result),
                "Tracked baseline library cannot be replaced by a clean scoped mirror")
        return result

    def make_plan(self):
        candidates, kept = [], Counter()
        for directory, subdirs, files in os.walk(self.lib, followlinks=False):
            subdirs[:] = [s for s in subdirs if not (Path(directory) / s).is_symlink()]
            for filename in files:
                path = Path(directory) / filename
                relative = str(path.relative_to(self.lib))
                name = module_of(relative)
                if name is None:
                    kept["unknown_artifact"] += 1
                    continue
                if name in self.protected or relative in self.protected_paths:
                    kept["scope_or_record_protected"] += 1
                    continue
                source = name.replace(".", "/") + ".lean"
                baseline = self.base_lib / relative
                if source not in self.tracked or not baseline.is_file() or baseline.is_symlink() or path.is_symlink():
                    kept["unknown_or_linked_source"] += 1
                    continue
                safe_path(self.project, path)
                safe_path(self.baseline, baseline)
                if not stat.S_ISREG(path.lstat().st_mode) or path.stat().st_nlink != 1:
                    kept["not_an_independent_regular_copy"] += 1
                    continue
                current, original = file_state(path), file_state(baseline)
                if current["sha256"] != original["sha256"]:
                    kept["different_or_partial_bytes"] += 1
                    continue
                candidates.append({"relative": relative, "module": name, "target": current, "baseline": original})
        return {"schema": "p24-scoped-baseline-recovery-v1", "status": "PLAN_ONLY",
                "project_root": str(self.project), "source_head": self.source_head,
                "baseline_root": str(self.baseline), "baseline_commit": BASELINE,
                "migration_receipt": {"path": str(self.receipt_path),
                                      "sha256": hashlib.sha256(self.receipt_raw).hexdigest()},
                "records_sha256": hashlib.sha256(self.records_raw).hexdigest(),
                "current_project_scope": sorted(self.nodes), "protected_module_count": len(self.protected),
                "migrated_records_preserved": len(self.receipt["migrated"]), "preserved_counts": dict(kept),
                "delete": sorted(candidates, key=lambda row: row["relative"]),
                "eligible_bytes": sum(r["target"]["bytes"] for r in candidates),
                "eligible_allocated_bytes": sum(r["target"]["allocated_bytes"] for r in candidates),
                "new_compile_credit": False, "kernel_credit": False}

    def check_inputs(self, sources=True):
        clean_head(self.baseline, BASELINE)
        require(sorted((self.project / ".lake/p2-private").glob("*records.json")) == self.registry_paths,
                "Registry file set changed during recovery")
        for raw_path, expected in self.input_states.items():
            require(file_state(Path(raw_path)) == expected, "Recovery input changed: " + raw_path)
        if sources:
            clean_head(self.project, self.source_head)
            for path, expected in self.source_hashes.items():
                require(digest(Path(path)) == expected, "Current project source changed: " + path)

    @contextmanager
    def lock(self, inherited_fd=None):
        path = self.project / ".lake/p2-private/p24-migration.lock"
        safe_path(self.project, path)
        require(path.is_file(), "Use the existing migration lock; do not allocate on a full disk")
        if inherited_fd is not None:
            info = os.fstat(inherited_fd)
            require(stat.S_ISREG(info.st_mode)
                    and (info.st_dev, info.st_ino) == tuple(identity(path)[:2]),
                    "Inherited lock descriptor does not identify the existing migration lock")
            fcntl.flock(inherited_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            yield
        else:
            with path.open("rb") as stream:
                fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
                yield

    def recover(self):
        self.check_inputs()
        for path in (self.out, self.mirror_root):
            safe_path(self.project, path)
            require(not path.exists(), "Use a fresh owned recovery/mirror attempt: " + str(path))
        require(self.plan["delete"], "No evidenced unprotected copies are available to free space")
        # Validate the entire deletion set before the first unlink. No output,
        # lock, temporary file, directory, or plan is allocated before freeing space.
        for row in self.plan["delete"]:
            for root, lib, key in ((self.project, self.lib, "target"),
                                   (self.baseline, self.base_lib, "baseline")):
                path = lib / row["relative"]
                safe_path(root, path)
                require(file_state(path) == row[key], "Planned copy changed: " + str(path))
        deleted, error = [], None
        try:
            for row in self.plan["delete"]:
                require(sorted((self.project / ".lake/p2-private").glob("*records.json")) == self.registry_paths,
                        "Registry file set changed before unlink")
                for path, expected in self.input_states.items():
                    require(identity(Path(path)) == expected["identity"], "Registry/receipt/snapshot changed")
                target, original = self.lib / row["relative"], self.base_lib / row["relative"]
                safe_path(self.project, target)
                safe_path(self.baseline, original)
                require(identity(original) == row["baseline"]["identity"], "Baseline copy changed before unlink")
                require(file_state(target) == row["target"], "Target copy changed before unlink")
                target.unlink()
                deleted.append(row)
            self.check_inputs()
        except BaseException as exc:
            error = exc
        result = {**self.plan, "status": "SCOPED_DUPLICATES_REMOVED" if error is None else "PARTIAL_RECOVERY_STOPPED",
                  "deleted_files": len(deleted), "deleted_bytes": sum(r["target"]["bytes"] for r in deleted),
                  "deleted": deleted, "free_bytes_after": shutil.disk_usage(self.project).free}
        if error is not None:
            result["error"] = str(error)
        if deleted or error is None:
            try:
                safe_path(self.project, self.out)
                self.out.mkdir(parents=True, exist_ok=False)
                write_new(self.out / "RECOVERY.json", result)
            except BaseException:
                print(json.dumps({"recovery_receipt_write_failed": result}), flush=True)
                raise
        if error is not None:
            raise error
        return result

    def build_mirror(self, full_checkout_limit=64 * 1024 * 1024):
        recovery_path = self.out / "RECOVERY.json"
        safe_path(self.project, recovery_path)
        recovered = json.loads(recovery_path.read_bytes())
        require(recovered.get("status") == "SCOPED_DUPLICATES_REMOVED"
                and recovered.get("project_root") == str(self.project)
                and recovered.get("baseline_root") == str(self.baseline)
                and recovered.get("baseline_commit") == BASELINE
                and recovered.get("records_sha256") == hashlib.sha256(self.records_raw).hexdigest()
                and recovered.get("migration_receipt") == self.plan["migration_receipt"],
                "Recovery receipt does not bind the current registry/migration/baseline")
        self.check_inputs(sources=False)
        runtime_head = clean_head(self.project)
        nodes = graph(self.project)
        selected_sources = {n.replace(".", "/") + ".lean" for n in nodes}
        selected_sources |= {".gitignore", "lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"}
        full = sum(self.tracked.values()) <= full_checkout_limit
        checkout_bytes = sum(size for path, size in self.tracked.items() if full or path in selected_sources)
        facets = []
        for name in sorted(nodes):
            for suffix in LOAD_SUFFIXES:
                relative = name.replace(".", "/") + suffix
                path = self.base_lib / relative
                if path.exists():
                    safe_path(self.baseline, path)
                    facets.append({"relative": relative, **file_state(path)})
        object_bytes = sum(r["bytes"] for r in facets)
        checker_copy_bytes = sum(r["bytes"] for r in facets if not (self.lib / r["relative"]).exists())
        require(shutil.disk_usage(self.project).free >= checkout_bytes + object_bytes + checker_copy_bytes + 256 * 1024 * 1024,
                "Insufficient free space for scoped mirror, missing checker copies, and 256 MiB reserve")
        safe_path(self.project, self.mirror_root)
        require(not self.mirror_root.exists(), "Mirror already exists; preserve it and choose a fresh attempt")
        self.mirror_root.parent.mkdir(parents=True, exist_ok=True)
        git(self.project, "clone", "--quiet", "--shared", "--no-hardlinks", "--no-checkout",
            str(self.baseline), str(self.mirror_root), allow_file=True)
        require((self.mirror_root / ".git").is_dir() and not (self.mirror_root / ".git").is_symlink(),
                "Clone must own its Git administration directory")
        old_objects = Path(git(self.baseline, "rev-parse", "--git-path", "objects").strip())
        old_objects = (self.baseline / old_objects).resolve()
        alternates = (self.mirror_root / ".git/objects/info/alternates").read_text().splitlines()
        require(alternates == [str(old_objects)], "Shared clone must borrow only its original baseline object root")
        if not full:
            git(self.mirror_root, "config", "core.sparseCheckout", "true")
            git(self.mirror_root, "config", "core.sparseCheckoutCone", "false")
            patterns = "".join("/" + path + "\n" for path in sorted(selected_sources & self.tracked.keys()))
            (self.mirror_root / ".git/info/sparse-checkout").write_text(patterns)
        git(self.mirror_root, "checkout", "--quiet", "--detach", BASELINE)
        mirror_lib = self.mirror_root / ".lake/build/lib/lean"
        safe_path(self.project, mirror_lib)
        mirror_lib.mkdir(parents=True)
        for row in facets:
            source, target = self.base_lib / row["relative"], mirror_lib / row["relative"]
            require(file_state(source) == {k: row[k] for k in ("identity", "sha256", "bytes", "allocated_bytes")},
                    "Baseline artifact changed before mirror copy")
            safe_path(self.project, target)
            target.parent.mkdir(parents=True, exist_ok=True)
            with source.open("rb") as incoming, target.open("xb") as outgoing:
                shutil.copyfileobj(incoming, outgoing, length=1024 * 1024)
            require(digest(target) == row["sha256"] and identity(source) == row["identity"],
                    "Mirror copy/source changed")
            require(identity(target)[:2] != row["identity"][:2], "Mirror must contain independent regular copies")
        clean_head(self.mirror_root, BASELINE)
        self.check_inputs(sources=False)
        require(clean_head(self.project) == runtime_head, "Runtime source changed during mirror creation")
        result = {"schema": "p24-scoped-baseline-mirror-v1", "status": "SCOPED_BASELINE_MIRROR_READY",
                  "project_root": str(self.project), "runtime_source_head": runtime_head,
                  "baseline_root": str(self.baseline), "baseline_commit": BASELINE,
                  "mirror_root": str(self.mirror_root), "checkout_mode": "full" if full else "sparse",
                  "git_administration": "independent .git directory",
                  "git_object_storage": "read-only alternates borrowed from original baseline by --shared",
                  "git_object_alternates": alternates,
                  "lean_object_storage": "independent regular copies; no symlinks or hardlinks",
                  "project_scope": sorted(nodes), "copied_facets": facets,
                  "checkout_bytes": checkout_bytes, "object_bytes": object_bytes,
                  "checker_missing_copy_bytes": checker_copy_bytes,
                  "new_compile_credit": False, "kernel_credit": False}
        write_new(self.out / "RUNTIME_SOURCE.json", {"source_head": runtime_head, "owned_branch": OWN_BRANCH,
                                                   "migration_receipt": self.plan["migration_receipt"]})
        write_new(self.out / "BASELINE_MIRROR.json", result)
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--baseline-root", type=Path, default=Path("/workspace/goldbach-p2"))
    parser.add_argument("--donor-root", type=Path, default=Path("/workspace/p2-private-20261124"))
    parser.add_argument("--external-snapshot", type=Path, required=True)
    parser.add_argument("--attempt", default="attempt-001")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true")
    mode.add_argument("--prepare-mirror", action="store_true")
    parser.add_argument("--lock-fd", type=int, help="Inherited descriptor for the existing migration lock")
    args = parser.parse_args()
    run = Recovery(args.project_root, args.baseline_root, args.donor_root, args.external_snapshot, args.attempt)
    print(json.dumps({k: v for k, v in run.plan.items() if k not in ("delete", "current_project_scope")}
                     | {"eligible_files": len(run.plan["delete"]), "project_count": len(run.nodes)}), flush=True)
    if not args.apply and not args.prepare_mirror:
        return 0
    with run.lock(args.lock_fd):
        if args.apply:
            result = run.recover()
            print(json.dumps({"status": result["status"], "deleted_files": result["deleted_files"],
                              "free_bytes_after": result["free_bytes_after"]}), flush=True)
        else:
            mirror = run.build_mirror()
            print(json.dumps({k: v for k, v in mirror.items() if k not in ("copied_facets", "project_scope")}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
