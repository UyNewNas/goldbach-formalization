#!/usr/bin/env python3
"""Rebind existing native inputs for the original P2.4 compact endpoint.

This new caller has its own actual source scope. It borrows pure byte selectors
and validators, never a Winner9/P6 acceptance label. It does not run Lean, Lake,
an object loader, or a native compiler. Historical quarantine remains binding.
Only a new private evidence directory is written; donor packages stay read-only.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import zipfile

sys.dont_write_bytecode = True
import repack_winner9_native_cache as carrier
from inspect_winner9_owner_native import git as readonly_git, imports as source_imports
from qualify_winner9_native_cache import LOAD_SUFFIXES, PROTOCOL, PROTOCOL_SHA256, core_header
from winner9_external_snapshot import (ExternalSnapshot, PhysicalHashes, PINS, SCHEMA,
                                      STATUS, native, require, signature)

ROOT = "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"
MEMBER_SHA = "f5b115fc46b5136a4d11df94052500acbc439f1190bb4cd61cdd1df02729f6da"
MANIFEST_SHA = "aff5553e88cb4434cbd2e2b9197e923a83b3312997cf822b822a790c43886ce9"
PRIOR_SHA = "0c0c5620ff231105d95149d631f55651454019b06c80e144e901d8d3b4a631cd"
MATHLIB_PIN = carrier.PINS["mathlib"]


def write_new(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def source_row(path: Path, package: str, hashes: PhysicalHashes) -> dict:
    raw = path.read_bytes()
    sha = hashlib.sha256(raw).hexdigest()
    require(hashes.digest(path) == sha, "Source changed during census: " + str(path))
    return {"package": package, "source": str(path.resolve()), "source_sha256": sha,
            "source_bytes": len(raw), "git_blob_sha1": carrier.blob_sha(raw),
            "direct_imports": source_imports(raw.decode())}


def project_census(project: Path, hashes: PhysicalHashes) -> tuple[dict, list[str]]:
    nodes, order, active = {}, [], set()

    def visit(name: str) -> None:
        require(name not in active, "Project import cycle: " + name)
        if name in nodes:
            return
        path = project / (name.replace(".", "/") + ".lean")
        row = source_row(path, "project", hashes)
        nodes[name] = row
        active.add(name)
        for dep in row["direct_imports"]:
            if dep.startswith("ImbalancedChen."):
                visit(dep)
        active.remove(name)
        order.append(name)

    visit(ROOT)
    return nodes, order


def original_map(setup: dict, row: dict, files: dict) -> dict:
    """Reconstruct the historical map from authenticated setup bytes, in order."""
    result = {}
    items = setup["importArts"].items() if isinstance(setup["importArts"], dict) else setup["importArts"]
    for name, groups in items:
        require(name not in result and isinstance(groups, list) and groups,
                "Duplicate or empty original import group: " + name)
        result[name] = []
        for group in groups:
            require(isinstance(group, list) and group, "Empty original physical subgroup")
            for text in group:
                path = Path(text)
                require(".." not in path.parts, "Unreviewed relative original import path")
                absolute = str(path if path.is_absolute() else Path(row["command"]["cwd"]) / path)
                require(absolute in files, "Original import lacks SHA receipt: " + absolute)
                result[name].append([absolute, files[absolute]["sha256"]])
    require(signature(result) == row["actual_import_map_sha256"], "Original actual-import-map SHA differs")
    return result


class P24Qualification:
    def __init__(self, args) -> None:
        self.args = args
        self.project = args.project_root.resolve(strict=True)
        self.donor = args.donor_root.resolve(strict=True)
        self.toolchain = args.toolchain_root.resolve(strict=True)
        self.out = args.out.resolve()
        require(not self.out.exists() and self.out.is_relative_to(self.project)
                and not self.out.is_relative_to(self.donor), "Use a new evidence directory inside the isolated P2.4 checkout")
        self.out.mkdir(parents=True)
        self.hashes = PhysicalHashes()
        self.bound, self.resolutions, self.local_blocked = {}, {}, {}
        self.rebindings = {}
        self.runtime_checks, self.abi_checks = [], []
        self.metadata_checks = {}
        self.checkpoint = args.checkpoint.resolve(strict=True)
        self.bind(self.checkpoint, "original-checkpoint", carrier.ARTIFACT["checkpoint_sha256"])
        require(self.checkpoint.stat().st_size == carrier.ARTIFACT["checkpoint_bytes"], "Original checkpoint length differs")
        self.cp = json.loads(self.checkpoint.read_text())
        require(self.cp["schema"] == "t01-coherent-build-checkpoint-v3"
                and self.cp["source_commit"] == carrier.ARTIFACT["producer_commit"]
                and self.cp["runtime_audit_valid"] is True
                and self.cp["all_dependency_source_pins_valid"] is True,
                "Original checkpoint identity/audits differ")
        self.member = self.read_anchor(args.member_receipt, MEMBER_SHA, "historical-member-install-receipt")
        require(self.member["schema"] == "r03-member-cdc-portable-seed-v1"
                and self.member["status"] == "EXACT_SOURCE_AND_RECURSIVE_IMPORT_BYTES_SEEDED_REQUIRES_INDEPENDENT_KERNEL_REPLAY"
                and Path(self.member["target_project"]).resolve() == self.donor
                and not self.member["blocked"] and not self.member["runtime_native_executable_reuse"],
                "Historical member receipt is not the recorded read-only donor")
        for key, expected in (("source_qualification_manifest", MANIFEST_SHA),
                              ("prior_common_import_crypto_audit", PRIOR_SHA)):
            pointer = self.member[key]
            require(pointer["sha256"] == expected, "Historical provenance pointer changed")
            self.bind(Path(pointer["path"]), "historical-" + key, expected)
        self.bind(PROTOCOL, "original-descriptor-validator", PROTOCOL_SHA256)
        spec = importlib.util.spec_from_file_location("p24_original_descriptor_protocol", PROTOCOL)
        require(spec is not None and spec.loader is not None, "Cannot load original descriptor validator")
        self.protocol = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.protocol)
        for path in (Path(__file__), Path(carrier.__file__), Path(sys.modules["winner9_external_snapshot"].__file__),
                     Path(sys.modules["inspect_winner9_owner_native"].__file__),
                     Path(sys.modules["qualify_winner9_native_cache"].__file__)):
            self.bind(path.resolve(), "qualification-tool")
        self.bind(Path(sys.modules["inspect_winner9_owner_native"].__file__), "fixed-source-parser", carrier.CENSUS_SCRIPT_SHA)
        self.packages = {row["name"]: (self.donor / ".lake/packages" / row["name"]).resolve(strict=True)
                         for row in self.cp["packages"]}
        self.check_packages()
        self.paths = [p / ".lake/build/lib/lean" for p in self.packages.values()
                      if (p / ".lake/build/lib/lean").is_dir()] + [self.toolchain / "lib/lean"]
        require(len(self.paths) == len(set(self.paths)), "Duplicate physical package roots")
        self.check_runtime()
        self.projects, self.project_order = project_census(self.project, self.hashes)
        self.nodes, self.order, active = {}, [], set()

        def visit(name: str) -> None:
            require(name not in active, "Native source import cycle: " + name)
            if name in self.nodes:
                return
            package = "LeanArchitect" if name.split(".")[0] == "Architect" else "goldbach"
            row = source_row(self.source_path(name, package), package, self.hashes)
            self.nodes[name] = row
            active.add(name)
            for dep in row["direct_imports"]:
                if native(dep):
                    visit(dep)
            active.remove(name)
            self.order.append(name)

        self.entries = sorted({dep for row in self.projects.values() for dep in row["direct_imports"] if native(dep)})
        for name in self.entries:
            visit(name)
        self.selected, self.omitted, _, self.excluded = carrier.select_payloads(self.cp, {"requested": self.nodes})
        self.archive = zipfile.ZipFile(args.archive.resolve(strict=True))
        # The fixed checkpoint authenticates each content-addressed ZIP member.
        # No claim is made that the whole multi-GB ZIP was freshly rehashed.
        self.scope = {"schema": "p24-original-compact-native-scope-v1", "roots": [ROOT],
                      "project_root": str(self.project), "project_head": self.git(self.project, "rev-parse", "HEAD"),
                      "project_modules": self.projects, "project_count": len(self.projects),
                      "direct_native_entries": self.entries, "native_modules": self.nodes,
                      "native_count": len(self.nodes), "compile_credit": False, "kernel_credit": False,
                      "source_compiler_or_object_loader_invocations": 0,
                      "historical_member_scope_relabelled": False}
        write_new(self.out / "SOURCE_SCOPE.json", self.scope)
        self.bind(self.out / "SOURCE_SCOPE.json", "actual-p24-source-scope")

    def freeze_current_core(self) -> None:
        """Freeze current implicit core inputs, without inventing historical SHAs.

        Original package setup maps omit implicit core imports. Their absence
        still blocks the quarantined Command leaf; this current-runtime census
        does not repair that historical absence or qualify the leaf.
        """
        modules, active = {}, set()

        def visit(name: str) -> None:
            require(name not in active, "Core source import cycle: " + name)
            if name in modules:
                return
            require(name.split(".", 1)[0] in {"Init", "Lean", "Std"}, "Unexpected core runtime dependency")
            source = self.source_path(name, "pinned-lean-toolchain")
            source_binding = self.bind(source, "current-core-runtime-source")
            imports, prelude = core_header(source.read_text())
            deps = imports + ([] if prelude or name == "Init" else ["Init"])
            active.add(name)
            for dep in deps:
                visit(dep)
            active.remove(name)
            stem = self.toolchain / "lib/lean" / name.replace(".", "/")
            obj = Path(str(stem) + ".olean")
            require(obj.is_file(), "Current implicit core object missing: " + name)
            objects = {}
            for suffix in LOAD_SUFFIXES:
                path = Path(str(stem) + suffix)
                if path.is_file():
                    objects[str(path.resolve())] = self.bind(path, "current-core-runtime-artifact")
            self.resolve(name, obj)
            modules[name] = {"source": str(source.resolve()), "source_binding": source_binding,
                             "imports": imports, "implicit_init": not prelude and name != "Init", "objects": objects}

        for root in ("Lean", "Std", "Init"):
            visit(root)
        path = self.out / "CURRENT_CORE_RUNTIME_INPUTS.json"
        write_new(path, {"schema": "p24-current-core-runtime-inputs-v1", "modules": modules,
                         "historical_per_core_hashes_claimed": False,
                         "native_provider_qualification": False, "compile_credit": False, "kernel_credit": False})
        self.bind(path, "current-core-runtime-census")
        print(json.dumps({"current_core_modules_frozen": len(modules), "historical_per_core_hashes_claimed": False}), flush=True)

    @staticmethod
    def git(root: Path, *args: str) -> str:
        return readonly_git(root, *args).decode().strip()

    def bind(self, path: Path, role: str, expected: str | None = None, size: int | None = None) -> dict:
        path = path.resolve(strict=True)
        require(path.is_file(), "Physical input is not a file: " + str(path))
        row = {"sha256": self.hashes.digest(path), "bytes": path.stat().st_size, "role": role}
        require(expected is None or row["sha256"] == expected, "Physical SHA differs: " + str(path))
        require(size is None or row["bytes"] == size, "Physical length differs: " + str(path))
        previous = self.bound.get(str(path))
        require(previous is None or all(previous[k] == row[k] for k in ("sha256", "bytes")),
                "Previously bound input changed: " + str(path))
        self.bound[str(path)] = previous or row
        return row

    def read_anchor(self, path: Path, expected: str, role: str) -> dict:
        self.bind(path, role, expected)
        return json.loads(path.read_text())

    def check_packages(self) -> None:
        lock = {row["name"]: row for row in json.loads((self.project / "lake-manifest.json").read_text())["packages"]}
        for row in self.cp["packages"]:
            name, root = row["name"], self.packages[row["name"]]
            require(row["pin_matches"] and row["tracked_sources_clean"] and lock[name]["rev"] == row["rev"]
                    and self.git(root, "rev-parse", "HEAD") == row["rev"], "Package pin differs: " + name)
            require(not self.git(root, "diff", "HEAD", "--"), "Tracked package source is modified: " + name)
        for name, pin in {**PINS, "mathlib": MATHLIB_PIN}.items():
            require(lock[name]["rev"] == pin, "Required package pin differs: " + name)

    def check_runtime(self) -> None:
        old = self.cp["runtime_state"]
        wrappers = {old["shadow"] + "/bin/" + name for name in old["tools"]}
        payloads = {p: sha for p, sha in old["runtime_sha256"].items() if p not in wrappers}
        require(len(payloads) == 11, "Original runtime payload census differs")
        for original, sha in payloads.items():
            name = Path(original).name
            path = self.toolchain / "bin" / ("lean" if name == "lean-runtime" else name)
            self.runtime_checks.append({"original": original, "path": str(path), **self.bind(path, "pinned-runtime", sha)})
        for row in self.cp["native_and_toolchain_library_ABI_receipts"]:
            original = row["original_path"]
            current = self.toolchain / "lib/lean" / Path(original).name if "/lib/lean/" in original else Path(original)
            observed = self.hashes.digest(current) if current.is_file() else None
            match = observed == row["sha256"]
            if row["role"] == "pinned-toolchain-shared-library-ABI":
                require(match, "Pinned Lean shared ABI differs: " + str(current))
                self.bind(current, row["role"], row["sha256"])
            self.abi_checks.append({"original": original, "current": str(current), "expected": row["sha256"],
                                    "observed": observed, "matched": match, "role": row["role"]})

    def source_path(self, name: str, package: str) -> Path:
        relative = Path(name.replace(".", "/") + ".lean")
        if package == "pinned-lean-toolchain":
            paths = [self.toolchain / "src/lean" / relative, self.toolchain / "src/lean/lake" / relative]
            return next((path for path in paths if path.is_file()), paths[0])
        require(package in self.packages, "Unexpected imported source package: " + package)
        return self.packages[package] / relative

    def artifact_path(self, name: str, original: str) -> Path:
        origin = self.cp["actual_import_sources"].get(name)
        require(origin is not None and "source" in origin, "Original imported source receipt missing: " + name)
        package = origin["package"]
        filename, stem = Path(original).name, name.rsplit(".", 1)[-1]
        require(filename.startswith(stem + "."), "Imported artifact has another module stem")
        suffix = filename[len(stem):]
        require(suffix in LOAD_SUFFIXES, "Unreviewed imported artifact suffix: " + suffix)
        require(package == "pinned-lean-toolchain" or package in self.packages, "Unselected artifact package")
        root = self.toolchain / "lib/lean" if package == "pinned-lean-toolchain" else self.packages[package] / ".lake/build/lib/lean"
        return root / (name.replace(".", "/") + suffix)

    def metadata(self, name: str, selected: dict) -> tuple[dict, dict, dict]:
        row = self.cp[selected["original_record_collection"]][selected["original_guarded_row_index"]]
        package = selected["package"]
        base = self.out / "original-metadata" / package
        marker = self.cp["runtime_state"]["root"] + "/.lake/packages/" + package + "/"
        for facet in selected["facets"]:
            original = facet["original_path"]
            require(original.startswith(marker), "Original facet has another package")
            if not original.endswith((".hash", ".trace", ".setup.json")):
                continue
            relative = Path(original[len(marker):])
            require(not relative.is_absolute() and ".." not in relative.parts, "Unsafe metadata path")
            path = base / relative
            raw = carrier.read_payload(self.archive, facet)
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("xb") as stream:
                stream.write(raw)
            self.bind(path, "original-metadata", facet["sha256"], facet["bytes"])
        stem = base / ".lake/build/lib/lean" / name.replace(".", "/")
        ir = base / ".lake/build/ir" / name.replace(".", "/")
        setup_path, trace_path = Path(str(ir) + ".setup.json"), Path(str(stem) + ".trace")
        setup, trace = json.loads(setup_path.read_text()), json.loads(trace_path.read_text())
        require(setup["name"] == name and setup["package"] == package and setup["options"] == {}
                and not setup["plugins"] and not setup["dynlibs"], "Original native setup options/plugins differ: " + name)
        require(trace["schemaVersion"] == "2025-09-10" and trace["synthetic"] is False,
                "Original trace is synthetic or incomplete: " + name)
        checks = self.protocol.lake_descriptor_binding(trace["outputs"], stem, ir)
        require(checks and all(r["matched"] for r in checks), "Original output descriptors do not bind: " + name)
        commands = selected["original_guarded_commands"]
        require(commands and all(c["tool"] == "lean" and "-t0" in c["command"] for c in commands)
                and all(not token.startswith("-D") for c in commands for token in c["input_args"]),
                "Original native compile command/profile differs: " + name)
        return row, setup, {"setup": str(setup_path), "trace": str(trace_path), "descriptor_checks": checks}

    def rebind(self, name: str) -> dict:
        require(name in self.selected, self.omitted.get(name, "NO_ORIGINAL_PROVIDER"))
        selected, wanted = self.selected[name], self.nodes[name]
        member = self.member["modules"].get(name)
        # The member installation is an additional authentic cross-check, not
        # this caller's scope restriction. A CP-only provider must still pass
        # every original guarded source/setup/map/runtime/current-object gate.
        if member is not None:
            require(member["source_sha256"] == wanted["source_sha256"], "Member source identity differs: " + name)
            observed_source = self.member["source_checks"].get(name)
            require(observed_source is not None and observed_source["sha256"] == wanted["source_sha256"]
                    and observed_source["actual_imports"] == wanted["direct_imports"], "Member source/import record differs: " + name)
        self.bind(Path(wanted["source"]), "selected-native-source", wanted["source_sha256"], wanted["source_bytes"])
        row, setup, metadata = self.metadata(name, selected)
        old_map = original_map(setup, row, self.cp["files"])
        if member is not None:
            require(member["actual_import_map_sha256_verified"] == signature(old_map), "Member/checkpoint import map differs: " + name)
        current_map = {}
        for imported, parts in old_map.items():
            require(not native(imported) or imported in self.nodes, "Actual native provider is outside current source closure: " + imported)
            origin = self.cp["actual_import_sources"].get(imported)
            require(origin is not None and "source" in origin, "Imported source lacks original receipt: " + imported)
            self.bind(self.source_path(imported, origin["package"]), "actual-imported-source", origin["source"]["sha256"], origin["source"]["bytes"])
            current_map[imported] = []
            for original, sha in parts:
                path = self.artifact_path(imported, original)
                self.bind(path, "actual-imported-artifact", sha, self.cp["files"][original]["bytes"])
                current_map[imported].append([str(path.resolve()), sha])
                rebound = {"module": imported, "current": str(path.resolve()), "sha256": sha,
                           "bytes": self.cp["files"][original]["bytes"]}
                previous = self.rebindings.setdefault(original, rebound)
                require(previous == rebound, "Conflicting physical original-to-current rebinding")
                if path.name.endswith(".olean"):
                    self.resolve(imported, path)
        own = {}
        lib = self.packages[wanted["package"]] / ".lake/build/lib/lean"
        stem = name.replace(".", "/")
        original_prefix = self.cp["runtime_state"]["root"] + "/.lake/packages/" + wanted["package"] + "/.lake/build/lib/lean/" + stem
        facets = {f["original_path"]: f for f in selected["facets"]}
        for suffix in LOAD_SUFFIXES:
            path, receipt = lib / (stem + suffix), facets.get(original_prefix + suffix)
            require((receipt is not None) == path.is_file(), "Current/original native loadable facet set differs: " + str(path))
            if receipt is not None:
                own[str(path.resolve())] = self.bind(path, "qualified-native-artifact", receipt["sha256"], receipt["bytes"])
        obj = lib / (stem + ".olean")
        require(str(obj.resolve()) in own, "Original native public object missing: " + name)
        self.resolve(name, obj)
        self.metadata_checks[name] = {"original_classification": selected["original_classification"],
                                     "original_import_map_sha256": signature(old_map), "actual_import_map_sha256": signature(current_map)}
        require(selected["original_classification"] == carrier.CLASSIFIED,
                "ORIGINAL_QUARANTINE_RETAINED_REQUIRES_INDEPENDENT_LEAF_RECEIPT:" + name)
        return {"schema": "p24-native-original-input-rebind-v1", "status": "EXACT_ORIGINAL_IMPORTS_REBOUND",
                "module": name, "source": wanted["source"], "source_sha256": wanted["source_sha256"],
                "objects": own, "original_classification": selected["original_classification"],
                "original_record_collection": selected["original_record_collection"],
                "original_guarded_row_index": selected["original_guarded_row_index"],
                "checkpoint_sha256": carrier.ARTIFACT["checkpoint_sha256"],
                "member_provider_present": member is not None,
                "member_receipt_sha256": MEMBER_SHA if member is not None else None,
                **metadata, "original_import_map_sha256": signature(old_map),
                "actual_import_map_sha256": signature(current_map), "new_source_compilation": False,
                "compile_credit": False, "kernel_credit": False, "historical_classifications_modified": False}

    def resolve(self, name: str, path: Path) -> None:
        key = str(path.resolve(strict=True))
        previous = self.resolutions.setdefault(name, key)
        require(previous == key, "Conflicting current import resolution: " + name)

    def recheck(self) -> None:
        self.check_packages()
        for path, row in self.bound.items():
            self.bind(Path(path), row["role"], row["sha256"], row["bytes"])
        for row in self.projects.values():
            require(self.hashes.digest(Path(row["source"])) == row["source_sha256"], "Project source changed during native qualification")

    def run(self) -> int:
        self.freeze_current_core()
        candidates = {}
        for index, name in enumerate(self.order, 1):
            try:
                candidates[name] = self.rebind(name)
            except (OSError, ValueError, KeyError) as error:
                self.local_blocked[name] = [str(error)]
            if index % 25 == 0:
                print(json.dumps({"examined": index, "native_total": len(self.order), "local_blockers": len(self.local_blocked)}), flush=True)
        table_path = self.out / "ORIGINAL_TO_CURRENT_IMPORTS.json"
        write_new(table_path, {"schema": "p24-original-to-current-physical-imports-v1", "paths": self.rebindings,
                               "reconstruction": "Retain each original setup importArts group and order; resolve relative paths against the checkpoint command cwd; substitute each absolute original path using this table."})
        table = self.bind(table_path, "actual-import-rebinding-table")
        blocked, qualified = {}, {}
        for name in self.order:
            reasons = list(self.local_blocked.get(name, []))
            failed = [d for d in self.nodes[name]["direct_imports"] if native(d) and d not in qualified]
            if failed:
                reasons.append("UNQUALIFIED_NATIVE_DEPENDENCIES:" + ",".join(failed))
            if reasons:
                blocked[name] = reasons
                continue
            receipt = self.out / "providers" / (name + ".json")
            candidates[name]["actual_import_rebinding_table"] = {"path": str(table_path), "sha256": table["sha256"]}
            write_new(receipt, candidates[name])
            self.bind(receipt, "native-provider-receipt")
            qualified[name] = {"status": "EXACT_ORIGINAL_IMPORTS_REBOUND", "receipt": str(receipt)}
        self.recheck()
        result = {"schema": "p24-native-input-qualification-v1",
                  "status": "NATIVE_QUALIFICATION_INCOMPLETE" if blocked else "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED",
                  "scope": str(self.out / "SOURCE_SCOPE.json"), "project_count": len(self.projects),
                  "native_count": len(self.nodes), "qualified": qualified, "blocked": blocked,
                  "outside_historical_member_install_scope": sorted(set(self.nodes) - set(self.member["modules"])),
                  "direct_blockers": self.local_blocked, "original_metadata_checks": self.metadata_checks,
                  "runtime_checks": self.runtime_checks, "abi_checks": self.abi_checks,
                  "new_source_compilations": 0, "object_loader_invocations": 0,
                  "compile_credit": False, "kernel_credit": False, "project_cache_acceptance": False,
                  "historical_member_scope_relabelled": False, "historical_classifications_modified": False,
                  "stock_lake_up_to_date_claimed": False, "donor_files_modified": False}
        receipt = self.out / "QUALIFICATION.json"
        write_new(receipt, result)
        write_new(self.out / "PHYSICAL_INPUTS.json", self.bound)
        self.archive.close()
        if blocked:
            print(json.dumps({"status": result["status"], "project_count": len(self.projects), "native_count": len(self.nodes),
                              "qualified_count": len(qualified), "direct_blockers": self.local_blocked,
                              "receipt": str(receipt), "compile_credit": False, "kernel_credit": False}), flush=True)
            return 2
        self.bind(receipt, "native-qualification-receipt")
        modules = {}
        for name in self.order:
            wanted = self.nodes[name]
            row = {"package": wanted["package"], "source": wanted["source"], "object": self.resolutions[name],
                   "imports": wanted["direct_imports"], "git_blob_sha1": wanted["git_blob_sha1"],
                   "dependency_signatures": {d: modules[d]["closure_signature"] for d in wanted["direct_imports"] if native(d)},
                   "provider": qualified[name]}
            bound = {k: row[k] for k in ("source", "object", "imports", "dependency_signatures", "provider")}
            bound.update(module=name, source_sha256=self.bound[row["source"]]["sha256"], object_sha256=self.bound[row["object"]]["sha256"])
            row["closure_signature"] = signature(bound)
            modules[name] = row
        lean = str(self.toolchain / "bin/lean")
        snapshot = {"schema": SCHEMA, "status": STATUS, "compile_credit": False, "kernel_credit": False,
                    "runtime": {"lean": lean, "leanchecker": str(self.toolchain / "bin/leanchecker"),
                                "sysroot": str(self.toolchain), "lean_path": list(map(str, self.paths)), "mathlib_commit": MATHLIB_PIN},
                    "packages": {name: {"root": str(self.packages[name]), "commit": pin} for name, pin in PINS.items()},
                    "qualification": {"path": str(receipt), "sha256": self.hashes.digest(receipt), "status": result["status"]},
                    "modules": modules, "files": self.bound, "resolutions": self.resolutions,
                    "caller_scope": "P2.4 original compact endpoint actual source closure; input qualification only"}
        snapshot["context_signature"] = signature(snapshot)
        pending = self.out / "PENDING_EXTERNAL_SNAPSHOT.json"
        write_new(pending, snapshot)
        ExternalSnapshot(pending, lean=lean, mathlib_pin=MATHLIB_PIN, project_lib=self.project / ".lake/p2-private/lib").verify()
        target = self.out / "EXTERNAL_SNAPSHOT.json"
        pending.rename(target)
        print(json.dumps({"status": result["status"], "snapshot": str(target), "snapshot_sha256": self.hashes.digest(target),
                          "project_count": len(self.projects), "native_count": len(self.nodes),
                          "compile_credit": False, "kernel_credit": False}), flush=True)
        return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--donor-root", type=Path, default=Path("/workspace/blue-member-build"))
    parser.add_argument("--toolchain-root", type=Path, default=Path("/workspace/toolchains/lean-4.33.0-rc1-linux"))
    parser.add_argument("--checkpoint", type=Path, default=Path("/workspace/artifacts/t01-fifth-objects-42753193835-1/CHECKPOINT.json"))
    parser.add_argument("--archive", type=Path, default=Path("/workspace/artifacts/t01-fifth-objects-42753193835-1.zip"))
    parser.add_argument("--member-receipt", type=Path, default=Path("/workspace/artifacts/cdc-qualified-member/INSTALL_RECEIPT.json"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    existed = args.out.exists()
    try:
        return P24Qualification(args).run()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        failure = {"status": "NATIVE_QUALIFICATION_INCOMPLETE", "fatal_blocker": str(error),
                   "compile_credit": False, "kernel_credit": False, "project_cache_acceptance": False}
        path = args.out.resolve() / "FAILURE.json"
        # Initialization may reject an existing output directory. Never modify
        # that earlier evidence merely to report the rejection.
        if not existed and path.parent.is_dir() and not path.exists():
            write_new(path, failure)
            print(json.dumps({**failure, "evidence_directory": str(path.parent)}), flush=True)
        else:
            print(json.dumps(failure), flush=True)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
