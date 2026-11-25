#!/usr/bin/env python3
"""Serial P3.6 direct-Lean runner with isolated build outputs. Default action: preflight only.

No Lake builds, downloads, or writes to dependency checkouts are performed.
Examples (once the pinned runtime and project have been restored):
  python3 compile_p36_local.py ImbalancedChen.P5OriginalU5NativeRootCover
  python3 compile_p36_local.py ImbalancedChen.P5OriginalU5NativeRootCover \
      --build --strict-owned --verify-owned --source-manifest SOURCE_SELECTION.json

All generated objects, state, commands, and logs belong to --build-dir, whose
default is PROJECT/.lake/p36-build. That directory may be a caller-owned symlink
to a spacious temporary volume. Existing successful objects are reused only
when source, compiler/options, dependency signatures, and all object sidecars
match the recorded successful run.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
sys.setrecursionlimit(20000)

BASE = Path(__file__).resolve().parent
DEFAULT_PROJECT = BASE.parents[1]
DEFAULT_RUNTIME = Path("/workspace/library-files/p34-runtime")
TOOLCHAIN_PIN = "leanprover/lean4:v4.33.0-rc1"
LEAN_COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
REQUIRED_PINS = {
    "mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
    "goldbach": "09b97db5764ade1246bfb77206baa1b124760958",
}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def utcnow() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def digest_json(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temporary.replace(path)


def lean_code(text: str) -> str:
    """Remove comments and strings while retaining line boundaries."""
    out, pos, depth = [], 0, 0
    while pos < len(text):
        if text.startswith("/-", pos):
            depth += 1
            pos += 2
            out.append(" ")
        elif depth and text.startswith("-/", pos):
            depth -= 1
            pos += 2
            out.append(" ")
        elif depth:
            out.append("\n" if text[pos] == "\n" else " ")
            pos += 1
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            pos = len(text) if end == -1 else end
        elif text[pos] == '"':
            pos += 1
            while pos < len(text):
                if text[pos] == "\\":
                    pos += 2
                elif text[pos] == '"':
                    pos += 1
                    break
                else:
                    out.append("\n" if text[pos] == "\n" else " ")
                    pos += 1
            out.append(" ")
        else:
            out.append(text[pos])
            pos += 1
    if depth:
        raise ValueError("Unterminated Lean block comment")
    return "".join(out)


def parse_imports(text: str) -> list[str]:
    result = []
    pattern = r"(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\s+([^\n]+)"
    for match in re.finditer(pattern, lean_code(text)):
        for name in match.group(1).split():
            if name in {"all", "meta"}:
                continue
            if not MODULE.fullmatch(name):
                raise ValueError("Unsupported import token: " + name)
            if name not in result:
                result.append(name)
    return result


@dataclass
class Node:
    module: str
    package: str
    source: Path | None
    source_root: Path | None
    kind: str
    cached_object: Path | None = None
    imports: list[str] = field(default_factory=list)


class BuildGraph:
    def __init__(self, project: Path, packages: Path, core: Path):
        self.project, self.packages, self.core = project, packages, core
        self.package_roots = sorted(p for p in packages.iterdir() if p.is_dir()) if packages.is_dir() else []
        self.nodes: dict[str, Node] = {}
        self.order: list[str] = []
        self.blockers: list[dict] = []
        self.mathlib_importers: list[dict] = []
        self._visiting: list[str] = []
        self._done: set[str] = set()

    def resolve(self, module: str) -> Node:
        if not MODULE.fullmatch(module):
            raise ValueError("Invalid module name: " + module)
        relative = Path(module.replace(".", "/"))
        source = self.project / relative.with_suffix(".lean")
        if source.is_file():
            return Node(module, "project", source, self.project, "build")
        core_object = self.core / relative.with_suffix(".olean")
        if core_object.is_file():
            return Node(module, "core", None, None, "core", core_object)
        candidates = []
        for root in self.package_roots:
            source = root / relative.with_suffix(".lean")
            obj = root / ".lake/build/lib/lean" / relative.with_suffix(".olean")
            if source.is_file() or obj.is_file():
                kind = "cached" if obj.is_file() else "blocked" if root.name == "mathlib" else "build"
                candidates.append(Node(module, root.name, source if source.is_file() else None,
                                       root, kind, obj if obj.is_file() else None))
        if len(candidates) == 1:
            node = candidates[0]
            if node.kind == "blocked":
                self.blockers.append({"module": module, "reason": "missing_mathlib_cache",
                                      "source": str(node.source), "import_chain": self._visiting[:]})
            return node
        reason = "ambiguous_package_module" if candidates else "missing_module"
        self.blockers.append({"module": module, "reason": reason,
                              "candidates": [str(n.source_root) for n in candidates],
                              "import_chain": self._visiting[:]})
        return Node(module, "missing", None, None, "blocked")

    def collect(self, modules: list[str]) -> None:
        for module in modules:
            self.visit(module)

    def visit(self, module: str) -> None:
        if module in self._done:
            return
        if module in self._visiting:
            self.blockers.append({"module": module, "reason": "import_cycle",
                                  "import_chain": self._visiting[:] + [module]})
            return
        self._visiting.append(module)
        node = self.nodes.setdefault(module, self.resolve(module))
        if node.source is not None:
            text = node.source.read_text()
            node.imports = parse_imports(text)
            if module != "Init" and not re.search(r"(?m)^\s*prelude\b", lean_code(text)):
                node.imports = list(dict.fromkeys(["Init", *node.imports]))
            if "Mathlib" in node.imports:
                self.mathlib_importers.append({"module": module, "package": node.package,
                                               "source": str(node.source)})
            for imported in node.imports:
                self.visit(imported)
        self._visiting.pop()
        self._done.add(module)
        self.order.append(module)


def object_hashes(obj: Path) -> dict[str, str]:
    if not obj.is_file():
        return {}
    return {str(path): sha256(path) for suffix in ("", ".private", ".server")
            if (path := Path(str(obj) + suffix)).is_file()}


def can_reuse(record: dict, input_key: str, obj: Path) -> bool:
    return ("reuse_origin" not in record and record.get("exit_code") == 0 and record.get("input_key") == input_key
            and bool(record.get("objects")) and record["objects"] == object_hashes(obj))


def compile_command(lean: Path, node: Node, obj: Path, strict: bool) -> list[str]:
    command = [str(lean), "-t0", "-j1", "-R", str(node.source_root)]
    if strict:
        command.append("-DwarningAsError=true")
    return command + ["-o", str(obj), str(node.source)]


class Runner:
    def __init__(self, args):
        self.args = args
        self.project = args.project.resolve()
        self.packages = args.packages_dir.resolve()
        self.toolchain = args.toolchain_dir.resolve()
        self.build = (args.build_dir or self.project / ".lake/p36-build").resolve()
        for protected in (self.packages, self.toolchain):
            if self.build.is_relative_to(protected):
                raise ValueError("Build output must not be inside shared dependencies/toolchain")
        self.objdir = self.build / "lib/lean"
        self.run_dir = self.build / "runs" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        self.run_dir.mkdir(parents=True)
        self.report_path = self.run_dir / "report.json"
        self.state_path = self.build / "state.json"
        self.state = json.loads(self.state_path.read_text()) if self.state_path.is_file() else {"schema": 1, "modules": {}}
        if self.state.get("schema") != 1:
            raise ValueError("Unsupported build-state schema")
        self.report = {"schema": 1, "status": "PREFLIGHT", "started_utc": utcnow(),
                       "project": str(self.project), "build_dir": str(self.build),
                       "targets": args.modules, "strict_owned": args.strict_owned or args.verify_owned,
                       "scope": "Specified modules only; not a certificate of whole P3.6 closure",
                       "commands": [], "modules": {}, "blockers": []}
        self.graph = BuildGraph(self.project, self.packages, self.toolchain / "lib/lean")
        self.snapshots: dict[str, str] = {}
        self.snapshots[str(Path(__file__).resolve())] = sha256(Path(__file__).resolve())
        self.report["runner_sha256"] = self.snapshots[str(Path(__file__).resolve())]
        self.signatures: dict[str, str] = {}
        self.project_reuse: dict[str, dict] = {}
        self.env = os.environ.copy()
        roots = [self.objdir] + [p / ".lake/build/lib/lean" for p in self.graph.package_roots]
        roots.append(self.toolchain / "lib/lean")
        self.env.update(LEAN_PATH=os.pathsep.join(map(str, roots)), LEAN_SYSROOT=str(self.toolchain),
                        LEAN_NUM_THREADS="1", PATH=str(self.toolchain / "bin") + os.pathsep + self.env.get("PATH", ""))
        self.report["lean_path"] = list(map(str, roots))

    def save(self) -> None:
        write_json(self.report_path, self.report)
        write_json(self.build / "latest.json", {"status": self.report["status"], "report": str(self.report_path),
                                               "targets": self.args.modules, "updated_utc": utcnow()})

    def command(self, name: str, command: list[str], *, checked=True) -> tuple[int, str, dict]:
        log = self.run_dir / (name.replace("/", "_") + ".log")
        started = time.monotonic()
        with log.open("w") as handle:
            handle.write("command=" + json.dumps(command) + "\n")
            handle.flush()
            try:
                result = subprocess.run(command, cwd=self.project, env=self.env, stdout=handle,
                                        stderr=subprocess.STDOUT, timeout=self.args.timeout, text=True)
                code = result.returncode
            except subprocess.TimeoutExpired:
                handle.write("\nRunner: this runner's child exceeded its configured timeout.\n")
                code = 124
        body = log.read_text(errors="replace").split("\n", 1)[1]
        record = {"name": name, "command": command, "exit_code": code,
                  "elapsed_seconds": round(time.monotonic() - started, 3),
                  "log": str(log), "log_sha256": sha256(log)}
        self.report["commands"].append(record)
        self.save()
        if checked and code:
            raise RuntimeError(f"{name} failed with exit {code}; see {log}\n{body[-3000:]}")
        return code, body, record

    def check_configuration(self) -> None:
        blockers = self.report["blockers"]
        pin_file = self.project / "lean-toolchain"
        if not pin_file.is_file() or pin_file.read_text().strip() != TOOLCHAIN_PIN:
            blockers.append({"reason": "missing_or_different_toolchain_pin", "path": str(pin_file)})
        manifest_path = self.project / "lake-manifest.json"
        if not manifest_path.is_file():
            blockers.append({"reason": "missing_dependency_manifest", "path": str(manifest_path)})
            manifest = {"packages": []}
        else:
            manifest = json.loads(manifest_path.read_text())
            self.snapshots[str(manifest_path)] = sha256(manifest_path)
        actual = {p["name"]: p.get("rev") for p in manifest.get("packages", [])}
        for name, expected in REQUIRED_PINS.items():
            if actual.get(name) != expected:
                blockers.append({"reason": "dependency_pin_mismatch", "package": name,
                                 "expected": expected, "actual": actual.get(name)})
        self.report["dependency_pins"] = actual
        for package in manifest.get("packages", []):
            root = self.packages / package["name"]
            if not root.is_dir():
                blockers.append({"reason": "missing_package_checkout", "package": package["name"]})
                continue
            code, text, _ = self.command("pin-" + package["name"],
                ["git", "--no-optional-locks", "-C", str(root), "rev-parse", "HEAD"], checked=False)
            if code or text.strip() != package.get("rev"):
                blockers.append({"reason": "checkout_pin_mismatch", "package": package["name"],
                                 "expected": package.get("rev"), "actual": text.strip()})
            code, text, _ = self.command("clean-" + package["name"],
                ["git", "--no-optional-locks", "-C", str(root), "status", "--porcelain", "--untracked-files=no"], checked=False)
            if code or text.strip():
                blockers.append({"reason": "dirty_package_checkout", "package": package["name"]})
        lean = self.toolchain / "bin/lean"
        if not lean.is_file():
            blockers.append({"reason": "missing_compiler", "path": str(lean)})
        else:
            code, version, _ = self.command("lean-version", [str(lean), "--version"], checked=False)
            if code or "version 4.33.0-rc1," not in version or LEAN_COMMIT not in version:
                blockers.append({"reason": "compiler_version_mismatch", "actual": version.strip()})
            self.report["compiler"] = {"path": str(lean), "sha256": sha256(lean), "version": version.strip()}
            self.snapshots[str(lean)] = sha256(lean)
        if self.args.verify_owned:
            checker = self.toolchain / "bin/leanchecker"
            if not checker.is_file():
                blockers.append({"reason": "missing_kernel_checker", "path": str(checker)})
            else:
                self.snapshots[str(checker)] = sha256(checker)

    def check_source_manifest(self) -> None:
        if self.args.source_manifest is None:
            return
        manifest_path = self.args.source_manifest.resolve()
        manifest = json.loads(manifest_path.read_text())
        self.snapshots[str(manifest_path)] = sha256(manifest_path)
        self.report["source_manifest"] = {"path": str(manifest_path), "sha256": sha256(manifest_path)}
        for entry in manifest["sources"]:
            module, relative = entry["module"], entry["selected_path"]
            expected_path = module.replace(".", "/") + ".lean"
            path = self.project / relative
            if relative != expected_path or not path.resolve().is_relative_to(self.project):
                raise ValueError("Invalid selected_path for " + module)
            actual = sha256(path) if path.is_file() else None
            if actual != entry["selected_sha256"]:
                self.report["blockers"].append({"reason": "selected_source_hash_mismatch", "module": module,
                    "path": str(path), "expected": entry["selected_sha256"], "actual": actual})

    def check_native_aliases(self) -> None:
        """An untracked flattened native module must equal a pinned tracked source."""
        native = [n for n in self.graph.nodes.values() if n.package == "goldbach" and n.source]
        if not native:
            return
        root = native[0].source_root
        _, listing, _ = self.command("native-tracked-files",
            ["git", "--no-optional-locks", "-C", str(root), "ls-files", "-s"])
        tracked = {}
        for line in listing.splitlines():
            metadata, path = line.split("\t", 1)
            tracked[path] = metadata.split()[1]
        aliases = []
        for node in native:
            relative = node.source.relative_to(root).as_posix()
            if relative in tracked:
                continue
            exact_alias = "research/wu2008/src/" + relative
            choices = [exact_alias] if relative.startswith("MathlibNt/Wu2008DoubleSieve/") and exact_alias in tracked else []
            actual = sha256(node.source)
            matches = [name for name in choices if sha256(root / name) == actual]
            if not matches:
                self.report["blockers"].append({"reason": "unverified_native_source_alias",
                    "module": node.module, "source": str(node.source), "candidates": choices})
                continue
            self.snapshots[str(node.source)] = actual
            for match in matches:
                self.snapshots[str(root / match)] = actual
            aliases.append({"module": node.module, "source": str(node.source),
                "sha256": actual, "tracked_matches": [
                    {"path": name, "git_blob": tracked[name]} for name in matches]})
        self.report["native_research_aliases"] = aliases

    def check_import_resolution(self) -> None:
        """Bind cached/core modules to the same external paths Lean will select."""
        roots = [Path(p) for p in self.report["lean_path"][1:]]
        for name, node in self.graph.nodes.items():
            if node.kind not in {"cached", "core"}:
                continue
            relative = name.replace(".", "/") + ".olean"
            resolved = next((root / relative for root in roots if (root / relative).is_file()), None)
            if resolved is None or resolved.resolve() != node.cached_object.resolve():
                self.report["blockers"].append({"reason": "external_import_resolution_mismatch",
                    "module": name, "expected": str(node.cached_object),
                    "actual": str(resolved) if resolved else None})

    def prepare_verified_bundles(self) -> None:
        if self.report["blockers"]:
            return
        from project_cache_reuse import inspect_verified_leaf_bundle
        records = []
        for path in self.args.reuse_verified_bundle:
            record = inspect_verified_leaf_bundle(path.resolve(), self.graph,
                self.report["compiler"], self.report["dependency_pins"])
            if record["module"] in self.args.modules:
                raise ValueError("An owned target cannot bypass this run's strict verification")
            self.project_reuse[record["module"]] = record
            self.snapshots.update(record["evidence_sha256"])
            self.snapshots[record["receipt"]] = record["receipt_sha256"]
            records.append(record)
        self.report["transferred_verified_objects"] = records

    def preflight(self) -> None:
        self.check_configuration()
        self.check_source_manifest()
        self.graph.collect(self.args.modules)
        self.report["blockers"].extend(self.graph.blockers)
        self.check_native_aliases()
        self.check_import_resolution()
        for target in self.args.modules:
            if self.graph.nodes[target].package != "project":
                self.report["blockers"].append({"reason": "owned_target_not_in_project", "module": target})
        self.report["topological_order"] = self.graph.order
        self.report["full_mathlib_importers"] = self.graph.mathlib_importers
        self.report["counts"] = dict(Counter(node.kind for node in self.graph.nodes.values()))
        self.report["project_module_count"] = sum(n.package == "project" for n in self.graph.nodes.values())
        for name in self.graph.order:
            node = self.graph.nodes[name]
            item = {"package": node.package, "kind": node.kind, "imports": node.imports,
                    "source": str(node.source) if node.source else None,
                    "cached_object": str(node.cached_object) if node.cached_object else None}
            if node.source:
                item["source_sha256"] = sha256(node.source)
                self.snapshots[str(node.source)] = item["source_sha256"]
            if node.kind == "build":
                item["planned_command"] = compile_command(self.toolchain / "bin/lean", node,
                    self.objdir / (name.replace(".", "/") + ".olean"),
                    self.report["strict_owned"] and name in self.args.modules)
            self.report["modules"][name] = item
        self.prepare_verified_bundles()
        self.report["status"] = "BLOCKED" if self.report["blockers"] else "PREFLIGHT_READY_NOT_COMPILED"
        self.save()

    def local_object(self, module: str) -> Path:
        obj = self.objdir / (module.replace(".", "/") + ".olean")
        if not obj.resolve().is_relative_to(self.build):
            raise RuntimeError("Object path escapes this runner's output: " + str(obj))
        return obj

    def remove_local_object(self, obj: Path) -> None:
        for suffix in ("", ".private", ".server"):
            path = Path(str(obj) + suffix)
            if not path.resolve().is_relative_to(self.build):
                raise RuntimeError("Object sidecar escapes this runner's output: " + str(path))
            path.unlink(missing_ok=True)

    def build_modules(self) -> None:
        self.report["status"] = "BUILDING"
        self.objdir.mkdir(parents=True, exist_ok=True)
        temporary = self.build / "tmp"
        temporary.mkdir(exist_ok=True)
        self.env["TMPDIR"] = str(temporary)
        for name in self.graph.order:
            node = self.graph.nodes[name]
            item = self.report["modules"][name]
            imports = {dependency: self.signatures[dependency] for dependency in node.imports}
            if node.kind in {"cached", "core"}:
                local = self.local_object(name)
                if local.exists():
                    self.remove_local_object(local)
                    item["removed_owned_shadow"] = str(local)
                objects = object_hashes(node.cached_object)
                if not objects:
                    raise RuntimeError("Cached object disappeared: " + str(node.cached_object))
                self.snapshots.update(objects)
                self.signatures[name] = digest_json({"objects": objects, "imports": imports,
                                                     "source": item.get("source_sha256")})
                item["objects"] = objects
                item["action"] = "external_cache"
                continue
            strict = self.report["strict_owned"] and name in self.args.modules
            input_data = {"source": str(node.source), "source_sha256": sha256(node.source),
                          "compiler": self.report["compiler"], "strict": strict,
                          "imports": imports, "lean_path": self.report["lean_path"], "trust": 0, "threads": 1}
            key = digest_json(input_data)
            obj = self.local_object(name)
            previous = self.state["modules"].get(name, {})
            stricter_policy_reused = False
            # A dependency already compiled with warnings as errors also meets
            # the ordinary policy. Preserve its exact stronger key/signature;
            # this never lets an owned target bypass fresh verification.
            if name not in self.args.modules and not strict and previous.get("strict") is True:
                stricter_inputs = {**input_data, "strict": True}
                stricter_key = digest_json(stricter_inputs)
                if can_reuse(previous, stricter_key, obj):
                    strict, input_data, key = True, stricter_inputs, stricter_key
                    stricter_policy_reused = True
            if not (self.args.verify_owned and name in self.args.modules) and can_reuse(previous, key, obj):
                objects = previous["objects"]
                item.update(action="reused", input_key=key, previous_log=previous.get("log"), objects=objects)
                if stricter_policy_reused:
                    item.update(strict=True, reused_stricter_warning_policy=True)
                print("REUSE " + name, flush=True)
            elif name in self.project_reuse:
                donor = self.project_reuse[name]
                obj.parent.mkdir(parents=True, exist_ok=True)
                self.remove_local_object(obj)
                shutil.copyfile(donor["object"], obj)
                if sha256(obj) != donor["object_sha256"]:
                    raise RuntimeError("Donor object changed while copying: " + name)
                objects = object_hashes(obj)
                record = {**input_data, "input_key": key, "exit_code": 0, "objects": objects,
                          "reuse_origin": donor, "finished_utc": utcnow()}
                self.state["modules"][name] = record
                write_json(self.state_path, self.state)
                item.update(action="reused_verified_receipt" if "receipt" in donor
                            else "reused_trace_verified_donor", **record)
                print("REUSE_DONOR " + name, flush=True)
            else:
                obj.parent.mkdir(parents=True, exist_ok=True)
                self.remove_local_object(obj)
                command = compile_command(self.toolchain / "bin/lean", node, obj, strict)
                print("BUILD " + name, flush=True)
                code, body, stage = self.command("compile-" + name, command, checked=False)
                objects = object_hashes(obj) if code == 0 else {}
                if code == 0 and (not objects or sha256(node.source) != input_data["source_sha256"]):
                    code = 125
                record = {**input_data, **stage, "input_key": key, "exit_code": code,
                          "objects": objects, "finished_utc": utcnow()}
                self.state["modules"][name] = record
                write_json(self.state_path, self.state)
                item.update(action="compiled" if code == 0 else "failed", **record)
                self.save()
                if code:
                    self.remove_local_object(obj)
                    raise RuntimeError(f"Compilation failed for {name}, exit {code}; see {stage['log']}\n{body[-6000:]}")
            self.snapshots.update(objects)
            self.signatures[name] = digest_json({"input_key": key, "objects": objects})
            self.save()
        self.assert_snapshots()
        self.report["status"] = "COMPILED"
        self.save()

    def assert_snapshots(self) -> None:
        for path, expected in self.snapshots.items():
            if not Path(path).is_file() or sha256(Path(path)) != expected:
                raise RuntimeError("Input or object changed during this run: " + path)
        roots = [Path(p) for p in self.report["lean_path"]]
        for module, node in self.graph.nodes.items():
            relative = module.replace(".", "/") + ".olean"
            selected = next((root / relative for root in roots if (root / relative).is_file()), None)
            expected = node.cached_object if node.kind in {"cached", "core"} else self.local_object(module)
            if selected is None or selected.resolve() != expected.resolve():
                raise RuntimeError("Import resolution changed during this run: " + module)

    def verify_owned(self) -> None:
        modules = tuple(self.args.modules)
        for module in modules:
            relative = module.replace(".", "/") + ".olean"
            selected = next((Path(root) / relative for root in self.report["lean_path"]
                             if (Path(root) / relative).is_file()), None)
            if selected is None or selected.resolve() != self.local_object(module).resolve():
                raise RuntimeError("Owned import resolves outside this runner's object directory: " + module)
            _, log, _ = self.command("replay-" + module,
                [str(self.toolchain / "bin/leanchecker"), "--verbose", module])
            if "replaying " + module not in log.splitlines():
                raise RuntimeError("Missing exact kernel replay evidence for " + module)
        verification = self.project / "verification"
        sys.path.insert(0, str(verification))
        spec = importlib.util.spec_from_file_location("p36_continuation_verifier",
                                                     verification / "verify_part3_continuation.py")
        helper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(helper)
        for path in (verification / "verify_part3_continuation.py",
                     verification / "verify_part3_distribution.py",
                     self.project / helper.baseline.AUDIT, self.project / helper.baseline.LEXER):
            self.snapshots[str(path)] = sha256(path)
        audit = self.run_dir / "P36OwnedAudit.lean"
        audit.write_text(helper.render_audit(modules))
        self.snapshots[str(audit)] = sha256(audit)
        _, log, _ = self.command("owned-inventory-audit", [str(self.toolchain / "bin/lean"),
            "-t0", "-j1", "-DwarningAsError=true", "-R", str(self.run_dir), str(audit)])
        declarations, counts = helper.baseline.validate_inventory(log, modules=modules)
        self.assert_snapshots()
        write_json(self.run_dir / "declarations.json", declarations)
        self.report.update(status="VERIFIED_OWNED", declaration_count=len(declarations), module_counts=counts,
                           declarations_file=str(self.run_dir / "declarations.json"))
        self.save()

    def execute(self) -> int:
        try:
            self.preflight()
            if self.report["blockers"]:
                return 2
            if self.args.build:
                self.build_modules()
                if self.args.verify_owned:
                    self.verify_owned()
            return 0
        except Exception as error:
            self.report.update(status="FAILED", error=str(error))
            return 1
        finally:
            self.report["finished_utc"] = utcnow()
            self.save()
            print(json.dumps({"status": self.report["status"], "report": str(self.report_path),
                "counts": self.report.get("counts"), "project_module_count": self.report.get("project_module_count"),
                "blocker_count": len(self.report["blockers"]),
                "blockers": [{k: v for k, v in item.items() if k != "import_chain"}
                             for item in self.report["blockers"][:25]],
                "full_mathlib_importers": self.report.get("full_mathlib_importers", []),
                "error": self.report.get("error")}, indent=2, ensure_ascii=False))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+", help="Owned project modules, in dotted notation")
    parser.add_argument("--project", type=Path, default=DEFAULT_PROJECT)
    parser.add_argument("--packages-dir", type=Path, default=DEFAULT_RUNTIME / "project/.lake/packages")
    parser.add_argument("--toolchain-dir", type=Path, default=DEFAULT_RUNTIME / "lean-4.33.0-rc1-linux")
    parser.add_argument("--build-dir", type=Path)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--preflight", action="store_true", help="Default: inspect only; do not compile")
    action.add_argument("--build", action="store_true", help="Explicitly enable topological compilation")
    parser.add_argument("--strict-owned", action="store_true", help="Warnings are errors only for requested modules")
    parser.add_argument("--verify-owned", action="store_true", help="With --build, strictly compile, replay and audit owned modules")
    parser.add_argument("--source-manifest", type=Path, help="JSON with sources: module, selected_path, selected_sha256")
    parser.add_argument("--reuse-verified-bundle", type=Path, action="append", default=[],
                        help="Transferred strict/kernel/axiom receipt bundle for a project-independent module")
    parser.add_argument("--timeout", type=float, default=600, help="Seconds per spawned command (default 600)")
    args = parser.parse_args()
    args.modules = list(dict.fromkeys(args.modules))
    if not args.project.is_dir():
        parser.error("Project directory is missing; restore the project before preflight")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    return Runner(args).execute()


if __name__ == "__main__":
    raise SystemExit(main())
