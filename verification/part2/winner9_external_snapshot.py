#!/usr/bin/env python3
"""Check an explicitly qualified native environment; never qualify old objects.

The producer must first bind original checkpoint imports or a fresh private
compilation. This consumer freezes those receipts and actual files around a
project compile/replay batch. A matching source pin alone is insufficient.
Calls without an external snapshot do not instantiate this environment checker.
Both drivers also use its native-ancestry marker and the fixed source parser.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess

from inspect_winner9_owner_native import imports as source_imports

SCHEMA = "p2-winner9-qualified-native-environment-v1"
STATUS = "QUALIFIED_NATIVE_INPUTS_ONLY_NOT_PROOF_ACCEPTANCE"
PINS = {
    "goldbach": "09b97db5764ade1246bfb77206baa1b124760958",
    "LeanArchitect": "78dd66840d3efe8c824c699fc03381cec817c271",
}
PREFIXES = {"MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd", "Goldbach", "Architect"}
PROVIDER_STATUSES = {"EXACT_ORIGINAL_IMPORTS_REBOUND", "FRESH_PRIVATE_SOURCE_COMPILATION"}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def encoded(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def signature(value: object) -> str:
    return hashlib.sha256(encoded(value)).hexdigest()


def native(name: str) -> bool:
    return name.split(".", 1)[0] in PREFIXES


def native_imports(path: Path) -> list[str]:
    return [name for name in source_imports(path.read_text()) if native(name)]


def mark_project_nodes(nodes: dict, available: set[str] | None) -> None:
    """Mark actual native ancestry, rejecting an incomplete supplied snapshot."""
    visiting: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        require(name not in visiting, "Project import cycle: " + name)
        if name in done:
            return
        visiting.add(name)
        row = nodes[name]
        direct = native_imports(row["source"])
        if available is not None:
            require(set(direct) <= available, "Native import absent from external snapshot: " + name)
        for dep in row["deps"]:
            visit(dep)
        row["native_imports"] = direct
        row["requires_external"] = bool(direct) or any(nodes[dep]["requires_external"] for dep in row["deps"])
        visiting.remove(name)
        done.add(name)

    for name in nodes:
        visit(name)


class PhysicalHashes:
    """Reuse a SHA only while device/inode/size/mtime/ctime remain identical."""
    def __init__(self) -> None:
        self.values: dict[Path, tuple[tuple, str]] = {}

    @staticmethod
    def stamp(path: Path) -> tuple:
        info = path.stat()
        return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    def digest(self, path: Path) -> str:
        before = self.stamp(path)
        previous = self.values.get(path)
        if previous is not None and previous[0] == before:
            return previous[1]
        with path.open("rb") as stream:
            value = hashlib.file_digest(stream, "sha256").hexdigest()
        require(self.stamp(path) == before, "Physical file changed while hashing: " + str(path))
        self.values[path] = (before, value)
        return value


class ExternalSnapshot:
    def __init__(self, path: Path, *, lean: str, mathlib_pin: str, project_lib: Path) -> None:
        self.path = path.resolve(strict=True)
        self.hashes = PhysicalHashes()
        self.raw_sha256 = self.hashes.digest(self.path)
        self.value = json.loads(self.path.read_text())
        value = self.value
        require(value.get("schema") == SCHEMA and value.get("status") == STATUS,
                "External snapshot has not completed source/object/import/runtime qualification")
        require(value.get("compile_credit") is False and value.get("kernel_credit") is False,
                "An environment snapshot cannot grant proof credit")
        unsigned = {key: val for key, val in value.items() if key != "context_signature"}
        require(value.get("context_signature") == signature(unsigned), "External snapshot signature differs")
        self.context_signature = value["context_signature"]
        self.modules = value["modules"]
        self.files = value["files"]
        self.project_lib = project_lib.resolve()
        runtime = value["runtime"]
        require(Path(runtime["lean"]).resolve() == Path(lean).resolve(), "External snapshot selects another Lean executable")
        require(runtime["mathlib_commit"] == mathlib_pin, "External snapshot selects another Mathlib pin")
        require(runtime["lean"] in self.files and runtime["leanchecker"] in self.files,
                "External runtime binaries lack physical hash bindings")
        require(value["qualification"]["status"] == "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED",
                "Native prerequisite qualification is incomplete")
        require(value["qualification"]["path"] in self.files
                and self.files[value["qualification"]["path"]]["sha256"] == value["qualification"]["sha256"],
                "Native qualification receipt is not frozen")
        require(set(value["packages"]) == set(PINS), "Unexpected native package set")
        for package, pin in PINS.items():
            require(value["packages"][package]["commit"] == pin, "Native package pin changed: " + package)
        require(self.modules and all(native(name) for name in self.modules), "Unexpected external module scope")
        self.search_path = [self.project_lib] + [Path(p).resolve() for p in runtime["lean_path"]]
        require(len(self.search_path) == len(set(self.search_path)), "Repeated external search root")
        require(all(p.is_absolute() for p in self.search_path), "External search roots must be absolute")
        require(Path(runtime["sysroot"]).resolve() / "lib/lean" in self.search_path,
                "Pinned core Lean root must be explicit in the external search path")
        self.verify_structure()
        self.verify()

    def verify_structure(self) -> None:
        for path, row in self.files.items():
            require(Path(path).is_absolute() and len(row["sha256"]) == 64 and row["bytes"] >= 0,
                    "Malformed external physical file record")
        visiting: set[str] = set()
        done: set[str] = set()

        def visit(name: str) -> None:
            require(name not in visiting, "Native import cycle: " + name)
            if name in done:
                return
            visiting.add(name)
            row = self.modules[name]
            require(row["package"] in PINS and row["source"] in self.files
                    and row["object"] in self.files and row["object"].endswith(".olean"),
                    "Native source/object is not physically bound: " + name)
            require(row["provider"]["status"] in PROVIDER_STATUSES
                    and row["provider"]["receipt"] in self.files,
                    "Native object lacks its own qualification/compilation receipt: " + name)
            deps = [dep for dep in row["imports"] if native(dep)]
            require(set(deps) <= set(self.modules), "Incomplete native transitive closure: " + name)
            for dep in deps:
                visit(dep)
            wanted = {dep: self.modules[dep]["closure_signature"] for dep in deps}
            require(row["dependency_signatures"] == wanted, "Native dependency signature differs: " + name)
            bound = {key: row[key] for key in ("source", "object", "imports", "dependency_signatures", "provider")}
            bound.update(module=name, source_sha256=self.files[row["source"]]["sha256"],
                         object_sha256=self.files[row["object"]]["sha256"])
            require(row["closure_signature"] == signature(bound), "Native closure signature differs: " + name)
            visiting.remove(name)
            done.add(name)

        for name in self.modules:
            visit(name)
        require(set(self.modules) <= set(self.value["resolutions"]), "Missing actual native import resolutions")
        for name, row in self.modules.items():
            require(self.value["resolutions"][name] == row["object"], "Native imported object differs: " + name)

    def verify_resolutions(self) -> None:
        # Conservatively reject any earlier package directory, even if a
        # per-file lookup might skip it. This covers Lean's package-root choice
        # without silently treating later LEAN_PATH entries as file fallbacks.
        for name, expected in self.value["resolutions"].items():
            require(expected in self.files, "Unfrozen resolved import: " + name)
            relative = Path(name.replace(".", "/") + ".olean")
            found = None
            for root in self.search_path:
                candidate = root / relative
                if candidate.is_file():
                    found = candidate.resolve()
                    break
                if (root / name.split(".", 1)[0]).is_dir():
                    raise ValueError("Earlier incomplete package root shadows external module: " + name)
            require(found is not None and found == Path(expected).resolve(),
                    "Actual search root differs from qualified object: " + name)

    def verify(self) -> dict:
        require(self.hashes.digest(self.path) == self.raw_sha256, "External snapshot changed during the batch")
        for package, row in self.value["packages"].items():
            current = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=row["root"], text=True).strip()
            require(current == PINS[package], "Native source checkout changed: " + package)
        for path, row in self.files.items():
            actual = Path(path)
            require(actual.is_file() and actual.stat().st_size == row["bytes"]
                    and self.hashes.digest(actual) == row["sha256"], "External physical input changed: " + path)
        for name, row in self.modules.items():
            raw = Path(row["source"]).read_bytes()
            require(source_imports(raw.decode()) == row["imports"], "Native source imports differ: " + name)
            git_blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
            require(git_blob == row["git_blob_sha1"], "Native source Git blob changed: " + name)
        self.verify_resolutions()
        return self.binding()

    def environment(self, previous: dict) -> dict:
        env = dict(previous)
        env.pop("LEAN_SRC_PATH", None)
        env["LEAN_SYSROOT"] = self.value["runtime"]["sysroot"]
        env["LEAN_PATH"] = os.pathsep.join(map(str, self.search_path))
        return env

    def binding(self) -> dict:
        return {"schema": SCHEMA, "snapshot": str(self.path), "snapshot_sha256": self.raw_sha256,
                "context_signature": self.context_signature,
                "verification_helper_sha256": self.hashes.digest(Path(__file__).resolve()),
                "native_modules": sorted(self.modules),
                "lean_path": list(map(str, self.search_path)),
                "lean_sysroot": self.value["runtime"]["sysroot"]}
