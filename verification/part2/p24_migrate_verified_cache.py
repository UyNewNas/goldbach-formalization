#!/usr/bin/env python3
"""Transport already verified P2 records into the isolated P2.4 checkout.

The original source tree, objects, records and qualified external snapshot are
read-only. Each old project closure must pass the existing compilation-record
verifier before any migrated record is constructed. Only the project search
root may change. This invokes no source compiler, object loader or kernel.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from qualify_winner9_native_cache import LOAD_SUFFIXES, atomic_missing
from run_winner9_private_checks import LEAN, MATHLIB, PIN, closure_signature
from run_winner9_private_audit import project_nodes, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, PhysicalHashes, mark_project_nodes, require

ROOT = "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"
STATUS = "EXACT_PREVIOUSLY_VERIFIED_CACHE_TRANSPORT_NOT_NEW_COMPILATION"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def write_new(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def check_binding_delta(old: dict, new: dict, old_lib: Path, new_lib: Path) -> None:
    """A new project path is not a new native environment qualification."""
    require({k: v for k, v in old.items() if k != "lean_path"}
            == {k: v for k, v in new.items() if k != "lean_path"},
            "External bindings differ beyond the project search root")
    require(old["lean_path"] and new["lean_path"]
            and old["lean_path"][0] == str(old_lib.resolve())
            and new["lean_path"][0] == str(new_lib.resolve())
            and old["lean_path"][1:] == new["lean_path"][1:],
            "External native search roots changed")


def closure(nodes: dict, name: str) -> dict:
    result = {}

    def visit(module):
        if module in result:
            return
        for dep in nodes[module]["deps"]:
            visit(dep)
        result[module] = dict(nodes[module])

    visit(name)
    return result


class Migration:
    def __init__(self, args):
        self.project = args.project_root.resolve(strict=True)
        self.donor = args.donor_root.resolve(strict=True)
        self.safe_target(args.out.absolute())
        self.out = args.out.resolve()
        require(self.project != self.donor and not self.project.is_relative_to(self.donor)
                and not self.donor.is_relative_to(self.project), "Use disjoint old and new project roots")
        require(not self.out.exists() and self.out.is_relative_to(self.project),
                "Use a fresh migration evidence directory in the target checkout")
        self.old_lib = (self.donor / ".lake/p2-private/lib").resolve(strict=True)
        self.safe_target(self.project / ".lake/p2-private/lib")
        self.lib = (self.project / ".lake/p2-private/lib").resolve()
        require(self.lib.is_relative_to(self.project), "Target project library escapes its checkout")
        self.old_path = self.donor / ".lake/p2-private/records.json"
        self.path = self.project / ".lake/p2-private/records.json"
        self.safe_target(self.path)
        self.old_raw = self.old_path.read_bytes()
        self.target_raw = self.path.read_bytes() if self.path.exists() else None
        self.old_records = json.loads(self.old_raw)
        self.records = json.loads(self.target_raw) if self.target_raw is not None else {}
        require(isinstance(self.old_records, dict) and isinstance(self.records, dict), "Record registry is not an object")
        self.hashes = PhysicalHashes()
        self.bound, self.facet_sets, self.logical_paths = {}, {}, {}
        self.created, self.transfer_index, self.committed = {}, 0, False
        pin = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip()
        require(pin == PIN, "Mathlib checkout differs from the existing strict runner pin")
        self.toolchain = {"lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
                          "lean_binary_sha256": self.hashes.digest(Path(LEAN)), "mathlib_commit": pin}
        self.old_external = ExternalSnapshot(args.external_snapshot, lean=LEAN, mathlib_pin=PIN,
                                             project_lib=self.old_lib)
        self.external = ExternalSnapshot(args.external_snapshot, lean=LEAN, mathlib_pin=PIN,
                                         project_lib=self.lib)
        self.old_binding, self.binding = self.old_external.binding(), self.external.binding()
        check_binding_delta(self.old_binding, self.binding, self.old_lib, self.lib)
        self.nodes = project_nodes(self.project, ROOT)
        mark_project_nodes(self.nodes, set(self.external.modules))
        self.source_before = {}
        for name, node in self.nodes.items():
            self.source_before[name] = self.bind(node["source"], "target-source")
        self.bind(Path(LEAN), "pinned-Lean-runtime", self.toolchain["lean_binary_sha256"])
        for module in (sys.modules["run_winner9_private_checks"], sys.modules["run_winner9_private_audit"],
                       sys.modules["winner9_external_snapshot"], sys.modules["qualify_winner9_native_cache"]):
            self.bind(Path(module.__file__).resolve(), "unchanged-verification-helper")
        self.bind(Path(__file__).resolve(), "migration-script")
        self.out.mkdir(parents=True)
        self.lib.mkdir(parents=True, exist_ok=True)
        old_copy = self.out / "ORIGINAL_DONOR_RECORDS.json"
        atomic_missing(old_copy, self.old_raw, sha(self.old_raw))
        self.old_records_copy = {"path": str(old_copy), "sha256": sha(self.old_raw), "bytes": len(self.old_raw)}
        if self.target_raw is not None:
            atomic_missing(self.out / "ORIGINAL_TARGET_RECORDS.json", self.target_raw, sha(self.target_raw))
        self.migrated, self.retained, self.blocked = {}, {}, {}

    def safe_target(self, path: Path) -> None:
        """Reject symlinks at every owned destination component, even dangling ones."""
        path = path.absolute()
        require(path.is_relative_to(self.project), "Target path is outside its isolated checkout")
        current = self.project
        parts = path.relative_to(self.project).parts
        for index, part in enumerate(parts):
            current /= part
            require(not current.is_symlink(), "Target path contains a symlink: " + str(current))
            require(current.resolve().is_relative_to(self.project), "Target physical path escapes its checkout")
            if index < len(parts) - 1 and current.exists():
                require(current.is_dir(), "Target path ancestor is not a directory")

    def bind(self, path: Path, role: str, expected: str | None = None) -> dict:
        logical = str(path.absolute())
        path = path.resolve(strict=True)
        physical = str(path)
        require(self.logical_paths.setdefault(logical, physical) == physical,
                "Logical input path changed its physical resolution: " + logical)
        require(path.is_file(), "Bound input is not a file: " + str(path))
        row = {"sha256": self.hashes.digest(path), "bytes": path.stat().st_size, "role": role}
        require(expected is None or row["sha256"] == expected, "Physical input SHA differs: " + str(path))
        previous = self.bound.setdefault(str(path), row)
        require(all(previous[k] == row[k] for k in ("sha256", "bytes")), "Bound input changed: " + str(path))
        return previous

    @staticmethod
    def facets(lib: Path, name: str) -> dict:
        stem = lib / name.replace(".", "/")
        return {suffix: Path(str(stem) + suffix) for suffix in LOAD_SUFFIXES
                if Path(str(stem) + suffix).is_file()}

    def freeze_facets(self, lib: Path, name: str) -> dict:
        if lib == self.lib:
            for suffix in LOAD_SUFFIXES:
                self.safe_target(lib / (name.replace(".", "/") + suffix))
        files = self.facets(lib, name)
        require(".olean" in files, "Project public object is absent: " + name)
        key = (str(lib), name)
        suffixes = sorted(files)
        previous = self.facet_sets.setdefault(key, suffixes)
        require(previous == suffixes, "Project loadable facet set changed: " + name)
        return {suffix: {"path": str(path), **self.bind(path, "project-loadable-facet")}
                for suffix, path in files.items()}

    def frozen(self, root: Path, lib: Path, nodes: dict, external: dict) -> dict:
        project = {}
        for name, node in nodes.items():
            source = node["source"]
            obj = lib / (name.replace(".", "/") + ".olean")
            if lib == self.lib:
                self.safe_target(obj)
            project[name] = {"source": str(source.relative_to(root)),
                             "source_sha256": self.bind(source, "verified-project-source")["sha256"],
                             "object": str(obj), "object_sha256": self.bind(obj, "verified-project-object")["sha256"]}
        return {"project": project, "toolchain": self.toolchain,
                "lean_binary_sha256": self.hashes.digest(Path(LEAN)), "external_snapshot": external}

    def verify_old(self, name: str, target_closure: dict) -> tuple[dict, dict]:
        old_nodes = project_nodes(self.donor, name)
        old_frozen = self.frozen(self.donor, self.old_lib, old_nodes, self.old_binding)
        # No old dependency signature is synthesized before this check.
        verify_compilation(self.old_records, old_nodes, old_frozen)
        require(set(old_nodes) == set(target_closure), "Old/new project closure membership differs: " + name)
        for module, old_node in old_nodes.items():
            target = target_closure[module]
            require(old_node["deps"] == target["deps"]
                    and old_frozen["project"][module]["source_sha256"] == self.source_before[module]["sha256"],
                    "Old/new source or project imports differ: " + module)
            # Exact source bytes imply equality of native and ordinary imports
            # as well; compare the bytes directly in addition to their SHA.
            require(old_node["source"].read_bytes() == target["source"].read_bytes(),
                    "Old/new source bytes differ: " + module)
            self.freeze_facets(self.old_lib, module)
        return old_nodes, old_frozen

    def verify_dependency_facets(self, dependencies: dict) -> None:
        for module in dependencies:
            old = self.freeze_facets(self.old_lib, module)
            new = self.freeze_facets(self.lib, module)
            require(set(old) == set(new)
                    and all((old[s]["sha256"], old[s]["bytes"]) == (new[s]["sha256"], new[s]["bytes"])
                            for s in old),
                    "Old/new dependency loadable facets differ: " + module)

    def install_facet(self, name: str, source: Path, destination: Path, expected: str) -> None:
        """Create a destination from a private inode; track only our successful link."""
        self.safe_target(destination)
        destination.parent.mkdir(parents=True, exist_ok=True)
        self.safe_target(destination)
        self.transfer_index += 1
        temporary = self.out / "transfer" / str(self.transfer_index) / destination.name
        self.safe_target(temporary)
        atomic_missing(temporary, source.read_bytes(), expected)
        # Ownership comes from the private inode we created, never from a
        # destination pathname another writer may replace after the link.
        owned_state = temporary.stat()
        try:
            parent_fd = os.open(destination.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            try:
                resolved_parent = Path(f"/proc/self/fd/{parent_fd}").resolve(strict=True)
                require(resolved_parent == destination.parent.resolve()
                        and resolved_parent.is_relative_to(self.lib), "Opened destination parent escapes owned library")
                try:
                    os.link(temporary, destination.name, dst_dir_fd=parent_fd, follow_symlinks=False)
                except FileExistsError:
                    self.safe_target(destination)
                    require(self.hashes.digest(destination) == expected,
                            "Concurrent different destination is preserved: " + str(destination))
                else:
                    self.created[str(destination)] = {"module": name, "device": owned_state.st_dev,
                                                      "inode": owned_state.st_ino, "sha256": expected}
            finally:
                os.close(parent_fd)
        finally:
            temporary.unlink()
        self.safe_target(destination)

    def rollback(self, paths: set[str]) -> None:
        """Delete only our still-identical newly created facets, never earlier files."""
        issues = []
        for text in sorted(paths, reverse=True):
            row = self.created.get(text)
            if row is None:
                continue
            path = Path(text)
            try:
                self.safe_target(path)
                if path.exists():
                    state = path.stat()
                    require((state.st_dev, state.st_ino) == (row["device"], row["inode"])
                            and self.hashes.digest(path) == row["sha256"],
                            "Concurrent replaced/changed output is preserved: " + text)
                    path.unlink()
                self.created.pop(text)
                self.bound.pop(text, None)
                self.logical_paths.pop(text, None)
                self.facet_sets.pop((str(self.lib), row["module"]), None)
            except (OSError, ValueError) as error:
                issues.append(str(error))
        require(not issues, "Could not safely roll back new outputs: " + "; ".join(issues))

    def copy_facets(self, name: str) -> dict:
        old = self.freeze_facets(self.old_lib, name)
        for suffix in LOAD_SUFFIXES:
            self.safe_target(self.lib / (name.replace(".", "/") + suffix))
        current = self.facets(self.lib, name)
        require(set(current) <= set(old), "Extra current loadable facet: " + name)
        # Validate the whole destination set before writing any facet.
        for suffix, path in current.items():
            require(not path.is_symlink() and self.hashes.digest(path) == old[suffix]["sha256"],
                    "Existing different target facet is retained: " + str(path))
        copied = {}
        for suffix, row in old.items():
            source = Path(row["path"])
            destination = self.lib / (name.replace(".", "/") + suffix)
            self.install_facet(name, source, destination, row["sha256"])
            copied[suffix] = {"old": str(source), "new": str(destination),
                              **self.bind(destination, "transported-project-facet", row["sha256"])}
        require(set(self.facets(self.lib, name)) == set(old), "Transported facet set is incomplete: " + name)
        self.freeze_facets(self.lib, name)
        return copied

    def recheck(self) -> None:
        require(self.old_external.verify() == self.old_binding and self.external.verify() == self.binding,
                "External input binding changed during migration")
        check_binding_delta(self.old_binding, self.binding, self.old_lib, self.lib)
        require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN,
                "Mathlib pin changed during migration")
        for path, row in list(self.bound.items()):
            self.bind(Path(path), row["role"], row["sha256"])
        for logical, physical in self.logical_paths.items():
            path = Path(logical)
            require(str(path.resolve(strict=True)) == physical,
                    "Logical input path changed its physical resolution: " + logical)
            if path.is_relative_to(self.lib):
                self.safe_target(path)
        for (lib, name), suffixes in self.facet_sets.items():
            require(sorted(self.facets(Path(lib), name)) == suffixes, "Project loadable facet set changed: " + name)
        self.check_registries()

    def check_registries(self) -> None:
        self.safe_target(self.path)
        require(self.old_path.read_bytes() == self.old_raw, "Donor records changed during migration")
        require((self.path.read_bytes() if self.path.exists() else None) == self.target_raw,
                "Target records changed during migration")

    def run(self) -> dict:
        lock = self.project / ".lake/p2-private/p24-migration.lock"
        self.safe_target(lock)
        descriptor = os.open(lock, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            os.ftruncate(descriptor, 0)
            os.write(descriptor, ("P2.4 verified-cache migration PID " + str(os.getpid()) + "\n").encode())
            self.check_registries()
            try:
                return self.run_transaction()
            except BaseException:
                if not self.committed:
                    self.rollback(set(self.created))
                raise
        finally:
            os.close(descriptor)

    def run_transaction(self) -> dict:
        for name in self.nodes:  # project_nodes returns dependency-first order.
            target_closure = closure(self.nodes, name)
            created_before = set(self.created)
            try:
                try:
                    verify_compilation(self.records, target_closure,
                                       self.frozen(self.project, self.lib, target_closure, self.binding))
                except (OSError, ValueError, KeyError):
                    pass
                else:
                    for module in target_closure:
                        self.freeze_facets(self.lib, module)
                    self.retained[name] = "EXISTING_VALID_TARGET_RECORD_RETAINED"
                    continue
                old_nodes, old_frozen = self.verify_old(name, target_closure)
                deps = {n: row for n, row in target_closure.items() if n != name}
                verify_compilation(self.records, deps, self.frozen(self.project, self.lib, deps, self.binding))
                self.verify_dependency_facets(deps)
                copied = self.copy_facets(name)
                original = self.old_records[name]
                row = deepcopy(original)
                row.update({"source": str(self.nodes[name]["source"].relative_to(self.project)),
                            "object": str(self.lib / (name.replace(".", "/") + ".olean")),
                            "deps": {dep: self.records[dep]["object_sha256"] for dep in self.nodes[name]["deps"]},
                            "dependency_signatures": {dep: self.records[dep]["closure_signature"] for dep in self.nodes[name]["deps"]},
                            "new_strict_compile": False,
                            "provenance": "verified prior private closure, byte-exact transport to P2.4 project root"})
                if self.nodes[name]["requires_external"]:
                    row["external_snapshot"] = self.binding
                    row["external_check"] = {"status": "PASSED_BATCH_PRE_POST", "before": self.binding, "after": self.binding}
                row["closure_signature"] = closure_signature(row)
                tentative = {**self.records, name: row}
                verify_compilation(tentative, target_closure,
                                   self.frozen(self.project, self.lib, target_closure, self.binding))
                evidence = {"original_closure": list(old_nodes),
                            "original_closure_signatures": {module: self.old_records[module]["closure_signature"] for module in old_nodes},
                            "old_source_object_snapshot": old_frozen["project"],
                            "transported_facets": copied, "new_closure_signature": row["closure_signature"],
                            "new_source_compilation": False, "kernel_replay": False}
                # Commit this provisional item only after every fallible copy
                # and validation for the module has completed. Registry writes
                # remain deferred until the final whole-batch checks.
                self.records[name] = row
                self.migrated[name] = evidence
            except (OSError, ValueError, KeyError) as error:
                self.rollback(set(self.created) - created_before)
                self.blocked[name] = str(error)
        self.recheck()
        for name in [*self.migrated, *self.retained]:
            nodes = closure(self.nodes, name)
            verify_compilation(self.records, nodes, self.frozen(self.project, self.lib, nodes, self.binding))
        receipt = {"schema": "p24-verified-private-cache-transport-v1", "status": STATUS,
                   "root": ROOT, "project_root": str(self.project), "donor_root": str(self.donor),
                   "actual_project_scope": sorted(self.nodes), "toolchain": self.toolchain,
                   "original_records_snapshot": self.old_records_copy,
                   "original_records": {name: self.old_records[name] for name in self.migrated},
                   "old_external_binding": self.old_binding, "new_external_binding": self.binding,
                   "only_external_binding_change": "lean_path[0]: old private project library to new private project library",
                   "migrated": self.migrated, "retained": self.retained, "not_migrated": self.blocked,
                   "physical_files_before_and_after": self.bound,
                   "loadable_facet_sets_before_and_after": [{"lib": lib, "module": name, "suffixes": suffixes}
                                                            for (lib, name), suffixes in sorted(self.facet_sets.items())],
                   "new_source_compilations": 0, "object_loader_invocations": 0, "kernel_replays": 0,
                   "new_strict_compile_credit": False, "kernel_credit": False, "donor_modified": False}
        receipt_path = self.out / "MIGRATION.json"
        self.safe_target(receipt_path)
        write_new(receipt_path, receipt)
        binding = {"path": str(receipt_path), "sha256": self.hashes.digest(receipt_path)}
        for name in self.migrated:
            self.records[name]["verified_cache_migration"] = binding
        if self.migrated:
            temporary = self.path.with_suffix(".p24-migration.tmp")
            self.safe_target(temporary)
            write_new(temporary, self.records)
            # Recheck immediately before the sole published registry mutation.
            # A failure leaves only an uncommitted temp file and evidence.
            self.recheck()
            self.check_registries()
            self.safe_target(temporary)
            temporary.replace(self.path)
            self.committed = True
        return {"status": STATUS, "project_count": len(self.nodes), "migrated": len(self.migrated),
                "retained": len(self.retained), "not_migrated": len(self.blocked),
                "receipt": str(receipt_path), "new_source_compilations": 0, "kernel_replays": 0}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--donor-root", type=Path, required=True)
    parser.add_argument("--external-snapshot", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(Migration(args).run()), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
