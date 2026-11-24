#!/usr/bin/env python3
"""Recover selected original bytes and bind their actual private import context.

This is a private-environment adapter for the existing coherent-cache protocol.
It reuses the original Lake descriptor validator and the already reviewed byte
selector. Frozen P2_NATIVE_398/STORED_PARENT caller policies are not modified.
Its output qualifies inputs only; independent replay/owned-declaration audits
remain necessary. No action is taken merely by importing this module.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import time
import zipfile

import repack_winner9_native_cache as carrier
from inspect_winner9_owner_native import imports as source_imports, source_tokens
from winner9_external_snapshot import (ExternalSnapshot, PhysicalHashes, SCHEMA, STATUS, PINS,
                                      native, require, signature)

HERE = Path(__file__).resolve().parent
PROTOCOL = HERE.parents[1] / "docs/source-only/20261113-resume/coherent-cache-tools/checkpoint_original_protocol.py"
PROTOCOL_SHA256 = "cfcb50064a13632a4a0fa8372d27bf86dd91f92eb6c38482afa575cf34921aff"
LOAD_SUFFIXES = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def write(path: Path, value: object) -> None:
    require(not path.exists(), "Refusing to overwrite previous evidence: " + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def atomic_missing(path: Path, raw: bytes, expected: str) -> None:
    require(carrier.digest(raw) == expected, "Candidate payload SHA changed")
    if path.exists():
        require(path.is_file() and not path.is_symlink() and carrier.file_sha(path) == expected,
                "Existing different output must not be overwritten: " + str(path))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".tmp-{os.getpid()}")
    with temporary.open("xb") as stream:
        stream.write(raw)
    try:
        os.link(temporary, path)
    finally:
        temporary.unlink()


def safe_member(name: str) -> None:
    require(not PurePosixPath(name).is_absolute() and ".." not in PurePosixPath(name).parts,
            "Unsafe packet member")


def staged_facet(out: Path, package: str, name: str, original: str, old_root: str) -> Path:
    base = old_root + ("" if package == "project" else "/.lake/packages/" + package) + "/"
    require(original.startswith(base), "Original facet is outside its selected package")
    relative = original[len(base):]
    safe_member(relative)
    stems = [".lake/build/" + directory + "/" + name.replace(".", "/") + "."
             for directory in ("lib/lean", "ir")]
    require(any(relative.startswith(stem) for stem in stems), "Facet belongs to another module")
    require(not relative.endswith(carrier.EXECUTABLE_SUFFIXES), "System-native executable facet is not eligible")
    return out / "candidates" / package / relative


def stage(args) -> int:
    request_raw = args.request.read_bytes()
    request = json.loads(request_raw)
    carrier.validate_request(request)
    require(carrier.file_sha(args.census) == request["source_census"]["sha256"], "Actual source census changed")
    require(not args.out.exists(), "Use a fresh isolated staging directory")
    meta = args.packets / "part-000.zip"
    with zipfile.ZipFile(meta) as packet:
        require(len(packet.namelist()) == 4 and set(packet.namelist()) == {"CHECKPOINT.json", "REQUEST.json", "ORIGINAL_ARTIFACT_METADATA.json",
                                          "EXPORT_MANIFEST.json"}, "Unexpected metadata packet")
        require(packet.read("REQUEST.json") == request_raw, "Exported request differs from the actual selected request")
        raw_cp = packet.read("CHECKPOINT.json")
        require(len(raw_cp) == carrier.ARTIFACT["checkpoint_bytes"]
                and carrier.digest(raw_cp) == carrier.ARTIFACT["checkpoint_sha256"], "Wrong original checkpoint bytes")
        cp = json.loads(raw_cp)
        manifest = json.loads(packet.read("EXPORT_MANIFEST.json"))
        remote = json.loads(packet.read("ORIGINAL_ARTIFACT_METADATA.json"))
    carrier.validate_remote_metadata(remote)
    require(cp["runtime_audit_valid"] and cp["all_dependency_source_pins_valid"], "Original checkpoint audits failed")
    require(cp["schema"] == "t01-coherent-build-checkpoint-v3"
            and cp["source_commit"] == carrier.ARTIFACT["producer_commit"], "Original checkpoint producer changed")
    selected, omitted, payloads, excluded = carrier.select_payloads(cp, request)
    for row in selected.values():
        row["source_bytes_verified_during_export"] = True
    require(manifest["selected_modules"] == selected and manifest["not_exported"] == omitted
            and manifest["excluded_native_executable_facets"] == excluded
            and manifest["request_sha256"] == carrier.digest(request_raw), "Byte selection differs from the original checkpoint")
    require(manifest["original_artifact"] == carrier.ARTIFACT and manifest["cache_acceptance"] is False,
            "A byte export cannot supply cache acceptance")
    args.out.mkdir(parents=True)
    atomic_missing(args.out / "CHECKPOINT.json", raw_cp, carrier.ARTIFACT["checkpoint_sha256"])
    atomic_missing(args.out / "REQUEST.json", request_raw, carrier.digest(request_raw))
    atomic_missing(args.out / "SOURCE_CENSUS.json", args.census.read_bytes(), request["source_census"]["sha256"])
    write(args.out / "EXPORT_MANIFEST.json", manifest)
    write(args.out / "ORIGINAL_ARTIFACT_METADATA.json", remote)
    payload_destinations: dict[str, list[Path]] = {}
    for name, row in selected.items():
        for facet in row["facets"]:
            destination = staged_facet(args.out, row["package"], name, facet["original_path"], cp["runtime_state"]["root"])
            payload_destinations.setdefault(facet["payload"], []).append(destination)
        payload_destinations.setdefault(row["source"]["payload"], []).append(
            args.out / "original-sources" / (name.replace(".", "/") + ".lean"))
    seen = set()
    packet_checks = []
    for descriptor in manifest["payload_packets"]:
        safe_member(descriptor["file"])
        path = args.packets / descriptor["file"]
        require(path.stat().st_size == descriptor["bytes"] and carrier.file_sha(path) == descriptor["sha256"],
                "Packet transport bytes changed: " + path.name)
        with zipfile.ZipFile(path) as packet:
            names = packet.namelist()
            require(len(names) == len(set(names)), "Duplicate packet member")
            index = json.loads(packet.read("PACKET_INDEX.json"))
            require(index["request_sha256"] == carrier.digest(request_raw) and index["original_artifact"] == carrier.ARTIFACT,
                    "Packet belongs to another request")
            require(set(names) == {"PACKET_INDEX.json", *index["payloads"]}, "Unindexed packet member")
            for key, row in index["payloads"].items():
                require(key not in seen and key in payloads, "Duplicate/unrequested packet payload")
                expected = payloads[key]
                require(row == {"sha256": expected["sha256"], "bytes": expected["bytes"]}, "Packet index differs from original receipt")
                raw = carrier.read_payload(packet, expected)
                for destination in payload_destinations[key]:
                    atomic_missing(destination, raw, expected["sha256"])
                seen.add(key)
        require(carrier.file_sha(path) == descriptor["sha256"], "Packet changed during extraction")
        packet_checks.append(descriptor)
    require(seen == set(payloads), "Original selected payloads are missing")
    for name, row in selected.items():
        raw = (args.out / "original-sources" / (name.replace(".", "/") + ".lean")).read_bytes()
        wanted = request["requested"][name]
        require(carrier.blob_sha(raw) == wanted["git_blob_sha1"]
                and source_imports(raw.decode()) == wanted["direct_imports"], "Original source identity changed")
    write(args.out / "STAGED.json", {"schema": "p2-winner9-native-staging-v1", "status": "BYTES_ONLY_NOT_QUALIFIED",
          "request_sha256": carrier.digest(request_raw), "checkpoint_sha256": carrier.ARTIFACT["checkpoint_sha256"],
          "script_sha256": carrier.file_sha(Path(__file__)), "packets": packet_checks,
          "selected_modules": sorted(selected), "not_exported": omitted,
          "source_compiler_invocations": 0, "compile_credit": False, "kernel_credit": False,
          "original_classifications_modified": False})
    print(json.dumps({"stage": str(args.out), "modules": len(selected), "status": "BYTES_ONLY_NOT_QUALIFIED"}), flush=True)
    return 0


class Qualification:
    def __init__(self, args) -> None:
        self.args, self.stage = args, args.stage.resolve()
        self.project = args.project_root.resolve()
        self.private_lib = self.project / ".lake/p2-private/lib"
        self.active = self.stage / "active/lib"
        self.active.mkdir(parents=True, exist_ok=True)
        self.request = read(self.stage / "REQUEST.json")
        carrier.validate_request(self.request)
        require(carrier.file_sha(self.stage / "CHECKPOINT.json") == carrier.ARTIFACT["checkpoint_sha256"], "Original checkpoint changed")
        require(carrier.file_sha(self.stage / "SOURCE_CENSUS.json") == self.request["source_census"]["sha256"], "Actual source census changed")
        self.cp, self.census = read(self.stage / "CHECKPOINT.json"), read(self.stage / "SOURCE_CENSUS.json")
        self.selected, _, _, _ = carrier.select_payloads(self.cp, self.request)
        self.hashes = PhysicalHashes()
        self.bound: dict[str, dict] = {}
        self.resolutions: dict[str, str] = {}
        self.qualified: dict[str, dict] = {}
        self.blocked: dict[str, list[str]] = {}
        self.runtime_checks, self.abi_checks = [], []
        self.toolchain = args.toolchain_root.resolve()
        self.lean = self.toolchain / "bin/lean"
        self.packages = {}
        for name, locked in self.request["locked_packages"].items():
            choices = ([args.mathlib_root] if name == "mathlib" else
                       [args.baseline_root / ".lake/packages" / name, args.mathlib_root / ".lake/packages" / name])
            root = next((p.resolve() for p in choices if (p / ".git").exists()), None)
            require(root is not None, "Missing pinned package source/cache root: " + name)
            self.packages[name] = root
            self.check_package(name)
        self.paths = [self.active] + [root / ".lake/build/lib/lean" for name, root in self.packages.items()
                                      if name not in PINS] + [self.toolchain / "lib/lean"]
        self.env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, self.paths)), LEAN_SYSROOT=str(self.toolchain))
        self.env.pop("LEAN_SRC_PATH", None)
        # Reuse the byte-exact original helper; frozen caller policy modules are
        # deliberately not instantiated with a new caller/scope.
        require(carrier.file_sha(PROTOCOL) == PROTOCOL_SHA256, "Original descriptor helper changed")
        spec = importlib.util.spec_from_file_location("winner9_original_descriptor_protocol", PROTOCOL)
        self.protocol = importlib.util.module_from_spec(spec)
        require(spec.loader is not None, "Cannot load the original descriptor helper")
        spec.loader.exec_module(self.protocol)
        self.check_runtime()
        producer_copy = self.stage / "tooling" / ("qualifier-" + carrier.file_sha(Path(__file__)) + ".py")
        atomic_missing(producer_copy, Path(__file__).read_bytes(), carrier.file_sha(Path(__file__)))
        self.producer_copy = producer_copy
        for path, role in [(self.stage / "CHECKPOINT.json", "original-checkpoint"),
                           (self.stage / "REQUEST.json", "exact-request"), (self.stage / "SOURCE_CENSUS.json", "source-census"),
                           (self.stage / "STAGED.json", "byte-staging-receipt"), (self.stage / "EXPORT_MANIFEST.json", "byte-export-manifest"),
                           (PROTOCOL, "original-descriptor-validator"), (producer_copy, "qualification-adapter")]:
            self.bind(path, role)

    def check_package(self, name: str) -> None:
        root = self.packages[name]
        expected = self.request["locked_packages"][name]["rev"]
        require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() == expected,
                "Current package source pin changed: " + name)
        require(not subprocess.check_output(["git", "diff", "HEAD", "--"], cwd=root), "Current tracked package source is modified: " + name)

    def bind(self, path: Path, role: str, expected: str | None = None) -> dict:
        path = path.resolve(strict=True)
        previous = self.bound.get(str(path))
        if previous is not None:
            require(expected is None or previous["sha256"] == expected, "Two original inputs require different bytes at one current path")
            # This adapter is one batch. Recheck the complete shared inventory
            # immediately before/after every source process and before final
            # promotion, instead of restatting the same Mathlib import for each
            # of hundreds of original setup maps.
            return previous
        actual = self.hashes.digest(path)
        require(expected is None or actual == expected, "Physical source/object/runtime differs: " + str(path))
        row = {"sha256": actual, "bytes": path.stat().st_size, "role": role}
        self.bound[str(path)] = row
        return row

    def check_runtime(self) -> None:
        old = self.cp["runtime_state"]
        wrapper_paths = {old["shadow"] + "/bin/" + name for name in old["tools"]}
        payloads = {path: sha for path, sha in old["runtime_sha256"].items() if path not in wrapper_paths}
        require(len(payloads) == 11, "Original runtime payload census changed")
        for old_path, expected in payloads.items():
            name = Path(old_path).name
            current = self.toolchain / "bin" / ("lean" if name == "lean-runtime" else name)
            observed = self.bind(current, "pinned-runtime", expected)
            self.runtime_checks.append({"original": old_path, "path": str(current), **observed})
        for row in self.cp["native_and_toolchain_library_ABI_receipts"]:
            original = row["original_path"]
            current = (self.toolchain / "lib/lean" / Path(original).name
                       if "/lib/lean/" in original else Path(original))
            actual = self.hashes.digest(current) if current.is_file() else None
            match = actual == row["sha256"]
            if row["role"] == "pinned-toolchain-shared-library-ABI":
                require(match, "Pinned Lean shared ABI differs")
                self.bind(current, row["role"], row["sha256"])
            self.abi_checks.append({"original": original, "current": str(current), "expected": row["sha256"],
                                    "observed": actual, "matched": match, "role": row["role"]})
        # No system-native object/plugin/dynlib is installed by this adapter.
        # Host C library differences remain explicit, as in the existing private
        # member-cache qualifier; they are not erased or called exact matches.

    def source_path(self, name: str, package: str) -> Path:
        relative = Path(name.replace(".", "/") + ".lean")
        if package == "project":
            return self.project / relative
        if package == "pinned-lean-toolchain":
            paths = [self.toolchain / "src/lean" / relative, self.toolchain / "src/lean/lake" / relative]
            return next((path for path in paths if path.is_file()), paths[0])
        require(package in self.packages, "Unknown imported source package: " + package)
        return self.packages[package] / relative

    def current_artifact(self, name: str, old_path: str) -> Path:
        origin = self.cp["actual_import_sources"].get(name)
        require(origin is not None and "source" in origin, "Missing original actual imported source: " + name)
        package = origin["package"]
        stem = name.rsplit(".", 1)[-1]
        filename = Path(old_path).name
        require(filename.startswith(stem + "."), "Actual imported artifact has another module stem")
        suffix = filename[len(stem):]
        require(suffix in LOAD_SUFFIXES, "Unreviewed actual import artifact kind: " + suffix)
        relative = Path(name.replace(".", "/") + suffix)
        if native(name):
            require(name in self.request["requested"], "Native import outside the actual source closure")
            return self.active / relative
        if package == "project":
            return self.private_lib / relative
        if package == "pinned-lean-toolchain":
            return self.toolchain / "lib/lean" / relative
        require(package in self.packages, "Unknown imported artifact package")
        return self.packages[package] / ".lake/build/lib/lean" / relative

    def original(self, name: str) -> tuple[dict, dict, Path, Path]:
        selected = self.selected[name]
        row = self.cp[selected["original_record_collection"]][selected["original_guarded_row_index"]]
        base = self.stage / "candidates" / selected["package"] / ".lake/build"
        stem = base / "lib/lean" / name.replace(".", "/")
        ir = base / "ir" / name.replace(".", "/")
        for facet in selected["facets"]:
            path = staged_facet(self.stage, selected["package"], name, facet["original_path"], self.cp["runtime_state"]["root"])
            require(path.is_file() and path.stat().st_size == facet["bytes"]
                    and self.hashes.digest(path) == facet["sha256"], "Original candidate facet changed")
        setup_path, trace_path = Path(str(ir) + ".setup.json"), Path(str(stem) + ".trace")
        setup, trace = read(setup_path), read(trace_path)
        require(setup["name"] == name and setup["package"] == ("imbalancedChen" if selected["package"] == "project" else selected["package"])
                and setup["options"] == {} and not setup["plugins"] and not setup["dynlibs"],
                "Original setup options/plugin context is not eligible")
        require(trace["schemaVersion"] == "2025-09-10" and trace["synthetic"] is False,
                "Original trace is incomplete/synthetic")
        checks = self.protocol.lake_descriptor_binding(trace["outputs"], stem, ir)
        require(checks and all(check["matched"] for check in checks), "Original trace/output sidecars do not bind")
        commands = selected["original_guarded_commands"]
        require(commands and all(command["tool"] == "lean" and "-t0" in command["command"] for command in commands),
                "Original source compiler was not the guarded trust-zero process")
        if selected["package"] != "project":
            require(all(not token.startswith("-D") for command in commands for token in command["input_args"]),
                    "Original native compiler has an unexpected option override")
        return row, setup, setup_path, trace_path

    def inputs(self, name: str, row: dict, setup: dict, *, exact_original: bool) -> tuple[dict, dict]:
        mapped, old_map, current_map = dict(setup), {}, {}
        mapped["importArts"] = {}
        command = row["command"] if "command" in row else row["guarded_source_commands"][0]
        items = setup["importArts"].items() if isinstance(setup["importArts"], dict) else setup["importArts"]
        for imported, groups in items:
            require(isinstance(groups, list) and groups, "Empty actual import group")
            origin = self.cp["actual_import_sources"].get(imported)
            require(origin is not None and "source" in origin, "Unbound original imported source")
            self.bind(self.source_path(imported, origin["package"]), "actual-imported-source", origin["source"]["sha256"])
            old_map[imported], current_map[imported], mapped["importArts"][imported] = [], [], []
            for group in groups:
                require(isinstance(group, list) and group, "Empty physical import subgroup")
                current_group = []
                for old in group:
                    absolute = str(Path(command["cwd"]) / old) if not Path(old).is_absolute() else old
                    receipt = self.cp["files"].get(absolute)
                    require(receipt is not None, "Actual original import lacks its own SHA receipt")
                    current = self.current_artifact(imported, absolute)
                    bound = self.bind(current, "actual-imported-artifact", receipt["sha256"] if exact_original else None)
                    old_map[imported].append([absolute, receipt["sha256"]])
                    current_map[imported].append([str(current.resolve()), bound["sha256"]])
                    current_group.append(str(current.resolve()))
                    if current.suffix == ".olean":
                        previous = self.resolutions.setdefault(imported, str(current.resolve()))
                        require(previous == str(current.resolve()), "Actual imported object has conflicting providers")
                mapped["importArts"][imported].append(current_group)
        require(signature(old_map) == row["actual_import_map_sha256"], "Original actual-import map SHA differs")
        return mapped, current_map

    def source(self, name: str) -> Path:
        wanted = self.request["requested"][name]
        path = self.source_path(name, wanted["package"])
        self.bind(path, "selected-native-source", wanted["source_sha256"])
        raw = path.read_bytes()
        require(carrier.blob_sha(raw) == wanted["git_blob_sha1"]
                and source_imports(raw.decode()) == wanted["direct_imports"], "Selected native source/imports changed")
        return path

    def activate(self, name: str, stem: Path) -> dict:
        objects = {}
        for suffix in LOAD_SUFFIXES:
            original = Path(str(stem) + suffix)
            if not original.is_file():
                continue
            target = self.active / (name.replace(".", "/") + suffix)
            atomic_missing(target, original.read_bytes(), self.hashes.digest(original))
            objects[str(target.resolve())] = self.bind(target, "qualified-native-artifact")
        obj = self.active / (name.replace(".", "/") + ".olean")
        require(str(obj.resolve()) in objects, "Qualified native provider has no public object")
        self.resolutions[name] = str(obj.resolve())
        return objects

    def recheck(self) -> None:
        for path, row in self.bound.items():
            require(Path(path).stat().st_size == row["bytes"] and self.hashes.digest(Path(path)) == row["sha256"],
                    "Previously bound physical input changed: " + path)
        for name in self.packages:
            self.check_package(name)

    def qualify(self) -> int:
        attempt_root = self.stage / "qualifications"
        attempt_root.mkdir(exist_ok=True)
        attempt = attempt_root / f"attempt-{len(list(attempt_root.glob('attempt-*'))) + 1:03}"
        attempt.mkdir()
        fresh_count = 0
        native_order = [name for name in self.census["topological_order"] if native(name)]
        for name in native_order:
            path = self.source(name)
            deps = [dep for dep in self.request["requested"][name]["direct_imports"] if native(dep)]
            reasons = []
            if not all(dep in self.qualified for dep in deps):
                reasons.append("A_REQUIRED_NATIVE_PROVIDER_IS_NOT_YET_QUALIFIED")
            if name not in self.selected:
                reasons.append("NO_EXPORTED_ORIGINAL_PROVIDER_OR_SETUP")
            row = setup = setup_path = trace_path = None
            fresh = None
            if not reasons:
                fresh = self.existing_fresh(name)
            if not reasons:
                try:
                    if fresh is None:
                        row, setup, setup_path, trace_path = self.original(name)
                        require(self.selected[name]["original_classification"] == carrier.CLASSIFIED,
                                "ORIGINAL_QUARANTINE_RETAINED:" + self.selected[name]["original_classification"])
                        _, actual_imports = self.inputs(name, row, setup, exact_original=True)
                except (OSError, ValueError, KeyError) as error:
                    reasons.append(str(error))
            if reasons and self.args.compile_missing and fresh_count < self.args.max_fresh_modules and all(dep in self.qualified for dep in deps) and name in self.selected:
                fresh_count += 1
                fresh = self.compile_existing(name, attempt)
                if fresh is not None:
                    reasons = []
            if reasons:
                self.blocked[name] = reasons
                print("BLOCKED_NATIVE", name, reasons[0], flush=True)
                continue
            provider_path = attempt / "providers" / (name + ".json")
            if fresh is None:
                stem = self.stage / "candidates" / self.selected[name]["package"] / ".lake/build/lib/lean" / name.replace(".", "/")
                objects = self.activate(name, stem)
                self.bind(setup_path, "original-setup")
                self.bind(trace_path, "original-trace")
                provider = {"status": "EXACT_ORIGINAL_IMPORTS_REBOUND", "module": name,
                            "original_classification": self.selected[name]["original_classification"],
                            "original_record_collection": self.selected[name]["original_record_collection"],
                            "original_guarded_row_index": self.selected[name]["original_guarded_row_index"],
                            "source": str(path), "source_sha256": self.bound[str(path.resolve())]["sha256"],
                            "objects": objects, "original_setup": str(setup_path), "original_trace": str(trace_path),
                            "original_import_map_sha256": row["actual_import_map_sha256"],
                            "actual_import_map": actual_imports, "actual_import_map_sha256": signature(actual_imports),
                            "checkpoint_sha256": carrier.ARTIFACT["checkpoint_sha256"],
                            "new_source_compilation": False, "kernel_credit": False}
                write(provider_path, provider)
            else:
                provider = fresh
                provider_path = Path(fresh["receipt"])
            self.bind(provider_path, "native-provider-receipt")
            self.qualified[name] = {"status": provider["status"], "receipt": str(provider_path.resolve())}
            print("QUALIFIED_NATIVE", name, provider["status"], flush=True)
        self.recheck()
        result = {"schema": "p2-winner9-native-qualification-v1",
                  "status": "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED" if not self.blocked else "NATIVE_QUALIFICATION_INCOMPLETE",
                  "script_sha256": carrier.file_sha(Path(__file__)), "request_sha256": carrier.file_sha(self.stage / "REQUEST.json"),
                  "checkpoint_sha256": carrier.ARTIFACT["checkpoint_sha256"],
                  "qualified": self.qualified, "blocked": self.blocked, "runtime_checks": self.runtime_checks,
                  "abi_checks": self.abi_checks, "fresh_native_compilations": fresh_count,
                  "all_required_native_modules": native_order, "compile_credit": False, "kernel_credit": False,
                  "stock_lake_up_to_date_claimed": False, "source_or_baseline_modified": False,
                  "scope": "Actual import bytes for direct private Lean use; no Lake-cache/up-to-date or theorem acceptance claim"}
        receipt_path = attempt / "QUALIFICATION.json"
        write(receipt_path, result)
        if self.blocked:
            print(json.dumps({"status": result["status"], "qualified": len(self.qualified), "blocked": len(self.blocked),
                              "receipt": str(receipt_path)}), flush=True)
            return 2
        self.bind(receipt_path, "native-qualification-receipt")
        modules = {}
        for name in native_order:
            wanted = self.request["requested"][name]
            row = {"package": wanted["package"], "source": str(self.source_path(name, wanted["package"]).resolve()),
                   "object": str((self.active / (name.replace(".", "/") + ".olean")).resolve()),
                   "imports": wanted["direct_imports"], "git_blob_sha1": wanted["git_blob_sha1"],
                   "dependency_signatures": {dep: modules[dep]["closure_signature"] for dep in wanted["direct_imports"] if native(dep)},
                   "provider": self.qualified[name]}
            bound = {key: row[key] for key in ("source", "object", "imports", "dependency_signatures", "provider")}
            bound.update(module=name, source_sha256=self.bound[row["source"]]["sha256"], object_sha256=self.bound[row["object"]]["sha256"])
            row["closure_signature"] = signature(bound)
            modules[name] = row
        snapshot = {"schema": SCHEMA, "status": STATUS, "compile_credit": False, "kernel_credit": False,
                    "runtime": {"lean": str(self.lean), "leanchecker": str(self.toolchain / "bin/leanchecker"),
                                "sysroot": str(self.toolchain), "lean_path": list(map(str, self.paths)),
                                "mathlib_commit": self.request["locked_packages"]["mathlib"]["rev"]},
                    "packages": {name: {"root": str(self.packages[name]), "commit": pin} for name, pin in PINS.items()},
                    "qualification": {"path": str(receipt_path.resolve()), "sha256": carrier.file_sha(receipt_path), "status": result["status"]},
                    "modules": modules, "files": self.bound, "resolutions": self.resolutions}
        snapshot["context_signature"] = signature(snapshot)
        snapshot_path = attempt / "EXTERNAL_SNAPSHOT.json"
        write(snapshot_path, snapshot)
        checked = ExternalSnapshot(snapshot_path, lean=str(self.lean), mathlib_pin=snapshot["runtime"]["mathlib_commit"],
                                   project_lib=self.private_lib)
        checked.verify()
        print(json.dumps({"status": result["status"], "native_modules": len(modules), "snapshot": str(snapshot_path),
                          "snapshot_sha256": carrier.file_sha(snapshot_path), "compile_credit": False, "kernel_credit": False}), flush=True)
        return 0

    def existing_fresh(self, name: str) -> dict | None:
        """Reuse a real earlier private compile only with its original frozen inputs."""
        paths = sorted((self.stage / "qualifications").glob("attempt-*/fresh/" + name + "/receipt.json"), reverse=True)
        for path in paths:
            receipt = read(path)
            if receipt.get("status") != "FRESH_PRIVATE_SOURCE_COMPILATION" or receipt.get("exit_code") != 0:
                continue
            require(receipt["module"] == name and receipt["input_files_unchanged"] is True,
                    "Earlier fresh receipt lacks actual pre/post binding")
            source = self.source(name)
            require(receipt["source"] == str(source) and receipt["source_sha256"] == carrier.file_sha(source),
                    "Earlier fresh source identity differs")
            stem = path.parent / name.replace(".", "/")
            expected = [str(self.lean), "-t0", "-j1", "-M6144", "-DwarningAsError=true",
                        str(source), "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean",
                        "--setup", receipt["actual_setup"], "--json"]
            require(receipt["command"] == expected and receipt["cwd"] == str(self.project)
                    and receipt["lean_path"] == self.env["LEAN_PATH"] and receipt["lean_sysroot"] == self.env["LEAN_SYSROOT"],
                    "Earlier actual fresh compiler/root context differs")
            for item, row in receipt["input_files"].items():
                self.bind(Path(item), "resumed-fresh-actual-input", row["sha256"])
                require(Path(item).stat().st_size == row["bytes"], "Earlier fresh input length changed")
            for item, row in receipt["objects"].items():
                self.bind(Path(item), "qualified-native-artifact", row["sha256"])
            self.bind(Path(receipt["log"]), "fresh-native-compile-log", receipt["log_sha256"])
            self.bind(Path(receipt["producer_script"]), "fresh-native-producer-script", receipt["producer_script_sha256"])
            self.bind(Path(receipt["actual_setup"]), "fresh-native-actual-setup")
            for imported, parts in receipt["actual_import_map"].items():
                for item, sha in parts:
                    self.bind(Path(item), "actual-imported-artifact", sha)
                    if item.endswith(".olean"):
                        self.resolutions[imported] = item
            self.activate(name, stem)
            if name == "Architect.Command":
                self.freeze_core_imports("Lean")
            print("REUSED_FRESH_NATIVE_RECEIPT", name, str(path), flush=True)
            return receipt
        return None

    def compile_existing(self, name: str, attempt: Path) -> dict | None:
        """Strictly compile an already selected source after its cache check failed.

        Reuse the original source's exact setup structure, changing only physical
        import locations to already qualified current objects. The invoked Lean
        process therefore receives a complete recorded import map, not a guessed
        replacement theorem or a manufactured old-cache acceptance receipt.
        """
        row, setup, _, _ = self.original(name)
        source = self.source(name)
        mapped, actual = self.inputs(name, row, setup, exact_original=False)
        directory = attempt / "fresh" / name
        directory.mkdir(parents=True)
        setup_path = directory / "actual.setup.json"
        write(setup_path, mapped)
        self.bind(setup_path, "fresh-native-actual-setup")
        stem = directory / name.replace(".", "/")
        stem.parent.mkdir(parents=True, exist_ok=True)
        # Command is the one special originally quarantined module. Its raw
        # setup legitimately has no importArts; freeze the actual pinned Lean
        # source/object closure before invoking its selected source.
        if name == "Architect.Command":
            require(mapped["importArts"] == {} and mapped["isModule"] is True,
                    "Architect.Command no longer matches the independent leaf case")
            self.freeze_core_imports("Lean")
        physical_roles = {"selected-native-source", "actual-imported-source", "actual-imported-artifact",
                          "pinned-runtime", "pinned-toolchain-shared-library-ABI", "fresh-native-actual-setup",
                          "fresh-leaf-core-source", "fresh-leaf-core-artifact", "qualified-native-artifact",
                          "resumed-fresh-actual-input"}
        before = {path: {"sha256": item["sha256"], "bytes": item["bytes"]} for path, item in self.bound.items()
                  if item["role"] in physical_roles}
        command = [str(self.lean), "-t0", "-j1", "-M6144", "-DwarningAsError=true",
                   str(source), "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean",
                   "--setup", str(setup_path), "--json"]
        self.recheck()
        log = directory / "compile.log"
        print("COMPILE_EXISTING_NATIVE", name, flush=True)
        start = time.monotonic()
        with log.open("x") as stream:
            process = subprocess.run(command, cwd=self.project, env=self.env, stdout=stream, stderr=subprocess.STDOUT)
        self.recheck()
        receipt = {"schema": "p2-winner9-native-fresh-compile-v1", "module": name,
                   "status": "FRESH_PRIVATE_SOURCE_COMPILATION" if process.returncode == 0 else "FRESH_COMPILATION_FAILED",
                   "command": command, "cwd": str(self.project), "lean_path": self.env["LEAN_PATH"],
                   "lean_sysroot": self.env["LEAN_SYSROOT"], "exit_code": process.returncode,
                   "seconds": round(time.monotonic() - start, 3), "source": str(source),
                   "producer_script": str(self.producer_copy.resolve()), "producer_script_sha256": carrier.file_sha(self.producer_copy),
                   "source_sha256": carrier.file_sha(source), "actual_setup": str(setup_path),
                   "actual_import_map": actual, "input_files": before, "input_files_unchanged": True,
                   "log": str(log), "log_sha256": carrier.file_sha(log),
                   "original_classification_retained": self.selected[name]["original_classification"],
                   "original_checkpoint_cache_was_not_adopted_for_this_module": True, "kernel_credit": False}
        self.bind(log, "fresh-native-compile-log")
        if process.returncode != 0:
            write(directory / "receipt.json", receipt)
            return None
        receipt["objects"] = self.activate(name, stem)
        receipt["receipt"] = str((directory / "receipt.json").resolve())
        write(directory / "receipt.json", receipt)
        return receipt

    def freeze_core_imports(self, target: str) -> None:
        seen = set()

        def visit(name: str) -> None:
            if name in seen:
                return
            seen.add(name)
            require(name.split(".", 1)[0] in {"Init", "Lean", "Std"}, "Unexpected core leaf dependency")
            source = self.source_path(name, "pinned-lean-toolchain")
            self.bind(source, "fresh-leaf-core-source")
            text = source.read_text()
            deps = source_imports(text)
            if not any(line.strip() == "prelude" for line in source_tokens(text).splitlines()) and name != "Init":
                deps.append("Init")
            for dep in deps:
                visit(dep)
            stem = self.toolchain / "lib/lean" / name.replace(".", "/")
            require(Path(str(stem) + ".olean").is_file(), "Missing actual core object for fresh leaf")
            for suffix in LOAD_SUFFIXES:
                path = Path(str(stem) + suffix)
                if path.is_file():
                    self.bind(path, "fresh-leaf-core-artifact")
            self.resolutions[name] = str(Path(str(stem) + ".olean").resolve())

        visit(target)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    staging = commands.add_parser("stage", help="Verify and stage exact byte packets; no proof/cache credit")
    for flag in ("packets", "request", "census", "out"):
        staging.add_argument("--" + flag, type=Path, required=True)
    qualify = commands.add_parser("qualify", help="Rebind actual imports/runtime; optionally fill necessary cache misses")
    qualify.add_argument("--stage", type=Path, required=True)
    qualify.add_argument("--project-root", type=Path, default=Path.cwd())
    qualify.add_argument("--baseline-root", type=Path, default=Path("/workspace/goldbach-p2"))
    qualify.add_argument("--mathlib-root", type=Path, default=Path("/workspace/compile-deps/mathlib"))
    qualify.add_argument("--toolchain-root", type=Path, default=Path("/workspace/toolchains/lean-4.33.0-rc1-linux"))
    qualify.add_argument("--compile-missing", action="store_true", help="Compile only selected sources whose exact original cache cannot qualify")
    qualify.add_argument("--max-fresh-modules", type=int, default=1, help="Bound fresh work; default covers only the quarantined leaf")
    args = parser.parse_args()
    if args.command == "stage":
        return stage(args)
    require(args.max_fresh_modules >= 0, "Fresh module budget must be nonnegative")
    return Qualification(args).qualify()


if __name__ == "__main__":
    raise SystemExit(main())
