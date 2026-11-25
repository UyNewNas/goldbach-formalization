#!/usr/bin/env python3
"""Validate three original d734 records; rebind their two native descendants.

No Lean process, loader or proof replay is run. Objects are never written.
The old snapshot is historical evidence, not a currently valid snapshot: only
explicit caller-source changes outside the protected dependency closure are
allowed. The fresh snapshot passes the unchanged ExternalSnapshot consumer.
Run with compiler/registry writers idle, as for the existing cache adopter.

A reviewed temporary copy can run at the original HEAD before fetch:
  PYTHONPATH=<project>/verification/part2 python3 -B <script> capture ...
All repository discovery uses --project-root, never this script's location.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
import run_winner9_private_checks as checks
import run_winner9_private_audit as audit
import winner9_external_snapshot as consumer
import inspect_winner9_owner_native as parser_module
import p27_qualify_native_inputs as qualification_module
import qualify_winner9_native_cache as native_protocol
from p27_qualify_native_inputs import InputBindings, module_path, ordered_import_map, source_row
from run_winner9_private_audit import project_nodes, verify_compilation
from run_winner9_private_checks import LEAN, MATHLIB, PIN, closure_signature, json_digest
from winner9_external_snapshot import ExternalSnapshot, PhysicalHashes, native, require, signature

ROOT = "ImbalancedChen.P2PairedCertificateCompletion"
CURRENTCHEN = "ImbalancedChen.CurrentChenBuchstabRefinement"
MODULES = ("ImbalancedChen.Certificates.PairedV2", "ImbalancedChen.CurrentPairedBuchstabBridge",
           "ImbalancedChen.Certificates.PairedV2FullBuchstab")
REBOUND_MODULES = MODULES[1:]
RETAINED_MODULES = MODULES[:1]
NATIVE_MODULES = ("MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction",
                  "MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds",
                  "MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation")
ORIGINAL_JOB = "d734023ac6d243279c3f73e3308f111f"
ORIGINAL_COMMIT = "9c5a20ab9e13bc9393db8c9f5b0b0e4212006970"
ORIGINAL_PROJECT = "/workspace/p2-7-20261125"
ORIGINAL_SNAPSHOT_SHA = "0ed5929623bdf54314abbb31e75e5a23e4216796ff6cfd2e0fc1d3f69dec0b6e"
STRICT_FLAGS = ["-t0", "-j1", "-M12288", "-DwarningAsError=true", "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
FROZEN_HELPERS = ("run_winner9_private_checks.py", "run_winner9_private_audit.py", "winner9_external_snapshot.py",
                  "inspect_winner9_owner_native.py", "qualify_winner9_native_cache.py", "p27_qualify_native_inputs.py",
                  "adopt_p27_currentchen_cache.py")
CREDITS = {"new_strict_compile": False, "compile_credit": False, "source_compiler_invocations": 0,
           "object_loader_invocations": 0, "kernel_credit": False}
METADATA_ROLES = {"current-p27-scope", "actual-import-rebinding-table", "native-provider-receipt", "native-qualification-receipt"}


def encoded(value) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def json_value(raw: bytes):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "Duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique)


def git(root: Path, *arguments: str) -> bytes:
    return subprocess.check_output(["git", *arguments], cwd=root)


def write_exclusive(path: Path, raw: bytes) -> None:
    with path.open("xb") as stream:
        try:
            stream.write(raw)
            stream.flush()
        except BaseException:
            # The exclusive open succeeded, so this partial file belongs to
            # this operation. Never remove a pre-existing path after EEXIST.
            path.unlink(missing_ok=True)
            raise


def source_relative(name: str) -> str:
    return module_path(name) + ".lean"


def normalize(value, directory: Path):
    """Only the one known qualification directory may change its location."""
    prefix = str(directory)
    if isinstance(value, str):
        return "@p27-native-attempt" + value[len(prefix):] if value == prefix or value.startswith(prefix + "/") else value
    if isinstance(value, list):
        return [normalize(item, directory) for item in value]
    if isinstance(value, dict):
        pairs = [(normalize(key, directory), normalize(item, directory)) for key, item in value.items()]
        require(len({key for key, _ in pairs}) == len(pairs), "Qualification path normalization collision")
        return dict(pairs)
    return value


class HistoricalEnvironment:
    """Explicit historical structure, never an ExternalSnapshot.verify bypass."""
    def __init__(self, path: Path, project_lib: Path, hashes: PhysicalHashes):
        self.path = path.resolve(strict=True)
        self.hashes = hashes
        self.raw = self.path.read_bytes()
        self.raw_sha256 = sha(self.raw)
        require(self.raw_sha256 == ORIGINAL_SNAPSHOT_SHA, "Original snapshot fixed SHA differs")
        self.value = json_value(self.raw)
        value = self.value
        require(value.get("schema") == consumer.SCHEMA and value.get("status") == consumer.STATUS
                and value.get("compile_credit") is False and value.get("kernel_credit") is False,
                "Original snapshot qualification boundary differs")
        require(value.get("context_signature") == signature({k: v for k, v in value.items() if k != "context_signature"}),
                "Original snapshot context signature differs")
        self.context_signature = value["context_signature"]
        self.files, self.modules = value["files"], value["modules"]
        self.project_lib = project_lib.resolve()
        self.search_path = [self.project_lib, *[Path(p).resolve() for p in value["runtime"]["lean_path"]]]
        require(set(self.modules) == set(NATIVE_MODULES), "Original native module scope differs")
        require(len(self.search_path) == len(set(self.search_path)), "Repeated original search root")
        # The unchanged pure structure/resolution validators are reused, but no
        # old constructor/verify success is fabricated after a caller edit.
        ExternalSnapshot.verify_structure(self)

    def historical_binding(self) -> dict:
        return ExternalSnapshot.binding(self)


class Context(InputBindings):
    def __init__(self, args, *, capture: bool = False):
        self.project = args.project_root.resolve(strict=True)
        require(str(self.project) == ORIGINAL_PROJECT, "Only the original d734 project is supported")
        self.lib = self.project / ".lake/p2-private/lib"
        require(self.lib.resolve(strict=True) == self.lib, "Private project library is redirected")
        self.registry = self.project / ".lake/p2-private/records.json"
        require(self.registry.is_file() and not self.registry.is_symlink(), "Private registry is absent or a symlink")
        self.registry_raw = self.registry.read_bytes()
        self.records = json_value(self.registry_raw)
        self.out = args.out.resolve()
        require(not args.out.is_symlink() and not self.out.exists() and self.out.is_relative_to(self.project)
                and not self.out.is_relative_to(self.lib), "Use a new isolated evidence directory")
        original_path = args.original_snapshot.resolve(strict=True)
        require(original_path == self.project / ".lake/p27-native/attempt-001/EXTERNAL_SNAPSHOT.json",
                "Unexpected original snapshot location")
        historical = HistoricalEnvironment(original_path, self.lib, PhysicalHashes())
        if capture:
            require(git(self.project, "rev-parse", "HEAD").decode().strip() == ORIGINAL_COMMIT,
                    "Capture must precede fetch/checkout at the original d734 HEAD")
            self.original_raw = self.registry_raw
            self.original_records_path = self.registry
            self.external = ExternalSnapshot(original_path, lean=LEAN, mathlib_pin=PIN, project_lib=self.lib)
        else:
            require(re.fullmatch(r"[0-9a-f]{64}", args.original_records_sha256) is not None,
                    "Supply the independently observed original registry SHA")
            self.original_records_path = args.original_records.resolve(strict=True)
            require(self.original_records_path != self.registry and not args.original_records.is_symlink(),
                    "Use the immutable original registry capture, not the live registry")
            self.original_raw = self.original_records_path.read_bytes()
            require(sha(self.original_raw) == args.original_records_sha256, "Original registry SHA differs from external capture")
            require(re.fullmatch(r"[0-9a-f]{64}", args.capture_manifest_sha256) is not None,
                    "Supply the independently observed capture manifest SHA")
            require(args.external_snapshot.resolve(strict=True) != original_path, "A fresh qualified snapshot is required")
            self.external = ExternalSnapshot(args.external_snapshot, lean=LEAN, mathlib_pin=PIN, project_lib=self.lib)
        super().__init__(self.external.hashes)
        historical.hashes = self.hashes
        self.old = historical
        self.old_binding = self.old.historical_binding()
        self.new_binding = self.external.binding()
        self.original_records = json_value(self.original_raw)
        require(isinstance(self.original_records, dict) and isinstance(self.records, dict), "Malformed compile registry")
        require(not self.out.is_relative_to(original_path.parent)
                and not self.out.is_relative_to(self.external.path.parent)
                and not self.out.is_relative_to(self.original_records_path.parent)
                and all(not self.out.is_relative_to(Path(p["root"]).resolve()) for p in self.external.value["packages"].values()),
                "Evidence directory overlaps an immutable supplier")
        self.bind(original_path, "immutable-original-snapshot", ORIGINAL_SNAPSHOT_SHA)
        self.bind(self.original_records_path, "immutable-original-registry", sha(self.original_raw))
        self.bind(self.external.path, "normally-qualified-current-snapshot", self.external.raw_sha256)
        self.git_blobs = {}
        require(git(self.project, "rev-parse", ORIGINAL_COMMIT + "^{commit}").decode().strip() == ORIGINAL_COMMIT,
                "Original source commit is unavailable")
        self.verify_helpers()
        self.scope = self.bound_json(self.old, "current-p27-scope")
        self.nodes = project_nodes(self.project, ROOT)
        self.protected = {}
        for name in MODULES:
            self.protected.update(project_nodes(self.project, name))
        require(len(self.nodes) == 81 and len(self.protected) == 13 and CURRENTCHEN in self.protected,
                "Unexpected P2.7 project/ancestor scope")
        self.current_rows, self.changed = {}, {}
        self.verify_sources(capture=capture)
        self.verify_old_files()
        ExternalSnapshot.verify_resolutions(self.old)
        self.project_snapshot = self.project_files()
        self.toolchain = self.original_records[MODULES[0]]["toolchain"]
        require(set(self.toolchain) == {"lean_version", "lean_binary_sha256", "mathlib_commit"}
                and isinstance(self.toolchain["lean_version"], str)
                and self.toolchain["lean_binary_sha256"] == self.hashes.digest(Path(LEAN))
                and self.toolchain["mathlib_commit"] == PIN
                and git(Path(MATHLIB), "rev-parse", "HEAD").decode().strip() == PIN,
                "Original/current compiler or Mathlib context differs")
        self.verify_original_records()
        if not capture:
            self.verify_capture(args.capture_manifest_sha256)
            self.compare_environments()
            self.verify_current_dependencies()

    def old_blob(self, relative: str) -> bytes:
        require(not Path(relative).is_absolute() and ".." not in Path(relative).parts, "Unsafe original Git path")
        if relative not in self.git_blobs:
            self.git_blobs[relative] = git(self.project, "cat-file", "blob", ORIGINAL_COMMIT + ":" + relative)
        return self.git_blobs[relative]

    def verify_helpers(self):
        loaded = {Path(m.__file__).name: Path(m.__file__).resolve() for m in
                  (checks, audit, consumer, parser_module, qualification_module, native_protocol)}
        for filename in FROZEN_HELPERS:
            relative = "verification/part2/" + filename
            expected = sha(self.old_blob(relative))
            self.bind(self.project / relative, "frozen-protocol-from-original-Git", expected)
            if filename in loaded:
                self.bind(loaded[filename], "actually-loaded-frozen-protocol", expected)

    def bound_json(self, environment, role):
        names = {"current-p27-scope": "SOURCE_SCOPE.json",
                 "actual-import-rebinding-table": "ORIGINAL_TO_CURRENT_IMPORTS.json",
                 "native-qualification-receipt": "QUALIFICATION.json"}
        require(role in names, "Unsupported current-attempt metadata role")
        # Inherited Winner9 files include their own qualification receipt and
        # 515 provider receipts. Never mistake a role label for unique scope.
        path = environment.path.parent / names[role]
        require(str(path) in environment.files and environment.files[str(path)].get("role") == role,
                "Missing exact current-attempt metadata: " + role)
        if role == "native-qualification-receipt":
            require(environment.value["qualification"]["path"] == str(path), "Wrong top-level qualification receipt")
        row = environment.files[str(path)]
        self.bind(path, role, row["sha256"], row["bytes"])
        return json_value(path.read_bytes())

    def verify_sources(self, *, capture):
        scope = self.scope
        require(scope["schema"] == "p27-actual-source-native-scope-v1" and scope["roots"] == [ROOT]
                and scope["project_root"] == str(self.project) and scope["project_count"] == 81
                and scope["native_count"] == 3 and set(scope["native_modules"]) == set(NATIVE_MODULES)
                and scope["compile_credit"] is False and scope["kernel_credit"] is False,
                "Original source census scope differs")
        require(set(scope["project_modules"]) == set(self.nodes), "Project source closure changed")
        for name, node in self.nodes.items():
            path = node["source"]
            require(not path.is_symlink() and path.resolve() == path, "Redirected caller source")
            old = self.old_blob(source_relative(name))
            expected = {"package": "project", "source": str(path), "source_sha256": sha(old), "source_bytes": len(old),
                        "git_blob_sha1": hashlib.sha1(b"blob " + str(len(old)).encode() + b"\0" + old).hexdigest(),
                        "direct_imports": parser_module.imports(old.decode())}
            require(scope["project_modules"][name] == expected, "Original source census differs from fixed Git blob: " + name)
            recorded = self.old.files.get(str(path), {})
            require(recorded.get("role") == "current-project-source"
                    and recorded.get("sha256") == sha(old) and recorded.get("bytes") == len(old),
                    "Original caller source lacks its exact frozen Git identity")
            current = source_row(path, "project", self.hashes)
            require(current["direct_imports"] == expected["direct_imports"], "Caller import graph changed: " + name)
            self.current_rows[name] = current
            self.bind(path, "current-caller-source", current["source_sha256"], current["source_bytes"])
            if current["source_sha256"] != expected["source_sha256"]:
                require(not capture and name not in self.protected, "Changed protected/capture source: " + name)
                self.changed[name] = {"source": str(path), "git_commit": ORIGINAL_COMMIT,
                                      "git_blob_sha1": expected["git_blob_sha1"], "old_sha256": sha(old), "old_bytes": len(old),
                                      "current_sha256": current["source_sha256"], "current_bytes": current["source_bytes"],
                                      "imports_unchanged": True, "outside_protected_closure": True}

    def verify_old_files(self):
        allowed = {row["source"] for row in self.changed.values()}
        for text, row in self.old.files.items():
            if text in allowed:
                require(row["role"] == "current-project-source", "Only caller source changes may be excepted")
            else:
                self.bind(Path(text), "unchanged-original-physical-input", row["sha256"], row["bytes"])

    def project_files(self):
        result = {}
        for name, node in self.protected.items():
            obj = self.lib / (module_path(name) + ".olean")
            require(obj.is_file() and not obj.is_symlink() and obj.resolve() == obj, "Redirected/missing protected project object")
            for suffix in native_protocol.LOAD_SUFFIXES:
                extra = self.lib / (module_path(name) + suffix)
                require(suffix == ".olean" or (not extra.exists() and not extra.is_symlink()),
                        "Extra unrecorded project facet: " + str(extra))
            source = node["source"]
            for path in (source, obj):
                self.bind(path, "protected-project-input")
            result[name] = {"source": str(source.relative_to(self.project)), "source_sha256": self.hashes.digest(source),
                            "object": str(obj), "object_sha256": self.hashes.digest(obj)}
        return result

    def frozen(self, binding):
        return {"project": self.project_snapshot, "toolchain": self.toolchain,
                "lean_binary_sha256": self.hashes.digest(Path(LEAN)), "external_snapshot": binding}

    def verify_original_records(self):
        verify_compilation(self.original_records, self.protected, self.frozen(self.old_binding))
        require({name for name in MODULES if self.protected[name]["requires_external"]} == set(REBOUND_MODULES),
                "Actual native ancestry differs from the two permitted rebind targets")
        for name in self.protected:
            row = self.original_records[name]
            actual = self.project_snapshot[name]
            require(row.get("source") == actual["source"] and row.get("object") == actual["object"],
                    "Original project record points at another source/object")
        for name in MODULES:
            row = self.original_records[name]
            require(row.get("new_strict_compile") is True and row.get("mathlib_commit") == PIN and row.get("lean") == "4.33.0-rc1",
                    "Missing original strict compilation authority: " + name)
            command = row.get("command", [])
            require(command == [LEAN, *STRICT_FLAGS, "-o", row["object"], row["source"]],
                    "Unexpected original strict command; any fallback flags require original-log review: " + name)
            attempts = row.get("attempts", [])
            require(attempts and attempts[-1] == {"command": command, "exit_code": 0, "log": row.get("log")},
                    "Original strict final attempt is not a recorded success")
            require(isinstance(row.get("log"), str)
                    and re.fullmatch(r"\.lake/p2-private/logs/" + re.escape(name) + r"\.attempt[1-9][0-9]*\.log", row["log"]),
                    "Original compile log coordinate differs")
            closure = set(project_nodes(self.project, name)) - {name}
            actual = {d: {k: self.original_records[d][k] for k in ("source_sha256", "object_sha256")} for d in closure}
            value = json_digest(actual)
            require(row.get("dependency_file_check") == {
                "modules": len(closure), "expected_sha256": value, "before_sha256": value, "after_sha256": value,
                "before_matches_records": True, "after_matches_records": True},
                "Original dependency file pre/post check differs: " + name)

    def compile_log_inventory(self, *, original_capture: bool):
        inventory, payloads = {}, {}
        for name in MODULES:
            record = self.original_records[name]
            paths = {record["log"], *[attempt["log"] for attempt in record["attempts"]]}
            for relative in sorted(paths):
                require(re.fullmatch(r"\.lake/p2-private/logs/" + re.escape(name) + r"\.attempt[1-9][0-9]*\.log", relative),
                        "Unsafe original attempt log coordinate")
                member = "COMPILE_LOG." + Path(relative).name
                path = self.project / relative if original_capture else self.original_records_path.parent / member
                require(path.is_file() and not path.is_symlink() and path.resolve() == path, "Missing/redirected captured compile log")
                data = path.read_bytes()
                self.bind(path, "capture-observed-original-compile-log", sha(data), len(data))
                inventory[relative] = {"module": name, "member": member, "sha256": sha(data), "bytes": len(data),
                                       "source_record_sha256": signature(record)}
                require(member not in payloads, "Duplicate original compile log member")
                payloads[member] = data
        return inventory, payloads

    def verify_capture(self, expected: str):
        path = self.original_records_path.parent / "CAPTURE.json"
        self.bind(path, "independently-anchored-original-capture", expected)
        raw = path.read_bytes()
        value = json_value(raw)
        require(value["schema"] == "p27-d734-original-registry-capture-v1"
                and value["status"] == "ORIGINAL_BYTES_CAPTURED_NOT_MIGRATED"
                and value["original_job"] == ORIGINAL_JOB and value["head"] == ORIGINAL_COMMIT
                and value["project"] == str(self.project) and value["registry_sha256"] == sha(self.original_raw)
                and value["registry_bytes"] == len(self.original_raw) and value["snapshot_sha256"] == ORIGINAL_SNAPSHOT_SHA
                and value["original_strict_modules"] == list(MODULES)
                and all(value[key] == wanted for key, wanted in CREDITS.items()),
                "Original capture manifest authority/scope differs")
        snapshot_copy = self.original_records_path.parent / "EXTERNAL_SNAPSHOT.json"
        self.bind(snapshot_copy, "captured-original-snapshot", ORIGINAL_SNAPSHOT_SHA, len(self.old.raw))
        inventory, self.log_payloads = self.compile_log_inventory(original_capture=False)
        require(value["compile_logs"] == inventory, "Captured original compile log inventory differs")
        require(value["log_hash_boundary"] == "Hashes observed during capture; original compiler records did not contain log hashes.",
                "Original log observation boundary differs")
        self.capture_manifest = {"path": str(path), "sha256": expected, "raw": raw}

    def facets(self, environment):
        result = {}
        for name, text in environment.value["resolutions"].items():
            require(text.endswith(".olean"), "Resolved public object suffix differs")
            result[name] = {}
            for suffix in native_protocol.LOAD_SUFFIXES:
                path = Path(text[:-6] + suffix)
                if path.exists() or path.is_symlink():
                    require(path.is_file(), "Non-file loadable facet")
                    physical = str(path.resolve(strict=True))
                    require(physical in environment.files, "Unbound loadable facet: " + str(path))
                    item = environment.files[physical]
                    self.bind(Path(physical), "actual-resolved-loadable-facet", item["sha256"], item["bytes"])
                    result[name][suffix] = {k: item[k] for k in ("sha256", "bytes")}
            require(".olean" in result[name], "Resolved module has no public object")
        return result

    def provider_context(self, environment, table):
        result = {}
        for name, module in environment.modules.items():
            path = Path(module["provider"]["receipt"])
            item = environment.files[str(path)]
            self.bind(path, "native-provider-receipt", item["sha256"], item["bytes"])
            value = json_value(path.read_bytes())
            require(value["schema"] == "p27-existing-native-provider-rebind-v1" and value["module"] == name
                    and value["status"] == "EXACT_ORIGINAL_IMPORTS_REBOUND"
                    and value["new_source_compilation"] is False and value["compile_credit"] is False
                    and value["kernel_credit"] is False, "Native provider scope/credit differs")
            setup_path = Path(value["setup"])
            require(str(setup_path) in environment.files, "Original provider setup is not frozen")
            setup_row = environment.files[str(setup_path)]
            self.bind(setup_path, "native-original-import-setup", setup_row["sha256"], setup_row["bytes"])
            original = ordered_import_map(json_value(setup_path.read_bytes()), value["source_runtime_event"]["cwd"],
                                          table["paths"], value["original_import_map_sha256"])
            current = {}
            for imported, parts in original.items():
                current[imported] = []
                for old_path, digest in parts:
                    entry = table["paths"][old_path]
                    require(entry["module"] == imported, "Imported artifact changed its module")
                    current[imported].append([entry["current"], digest])
            require(signature(current) == value["actual_import_map_sha256"], "Native current import map SHA differs")
            value["actual_import_map_sha256"] = "VERIFIED_MAP_WITH_EQUIVALENT_PHYSICAL_BYTES"
            result[name] = normalize(value, environment.path.parent)
        return result

    def import_table(self, environment):
        table = self.bound_json(environment, "actual-import-rebinding-table")
        require(table["schema"] == "p27-original-to-current-physical-imports-v1", "Unknown native import table")
        for original, row in table["paths"].items():
            name = row["module"]
            require(name in environment.value["resolutions"], "Unknown actual imported module")
            leaf = name.rsplit(".", 1)[-1]
            filename = Path(original).name
            require(filename.startswith(leaf + "."), "Original imported path belongs to another module")
            suffix = filename[len(leaf):]
            require(suffix in native_protocol.LOAD_SUFFIXES, "Unknown original imported facet")
            obj = environment.value["resolutions"][name]
            wanted = Path(obj[:-6] + suffix).resolve(strict=True)
            require(Path(row["current"]).resolve(strict=True) == wanted and str(wanted) in environment.files,
                    "Actual import table does not name the resolved facet")
            identity = environment.files[str(wanted)]
            require(all(row[k] == identity[k] for k in ("sha256", "bytes")), "Actual import facet identity differs")
            self.bind(wanted, "actual-native-import-map-entry", row["sha256"], row["bytes"])
        return table

    def qualification(self, environment, table):
        value = self.bound_json(environment, "native-qualification-receipt")
        require(value["schema"] == "p27-native-input-qualification-v1"
                and value["status"] == "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED"
                and value["roots"] == [ROOT] and value["project_count"] == 81 and value["native_count"] == 3
                and set(value["qualified"]) == set(NATIVE_MODULES) and value["blocked"] == {}
                and value["source_compiler_invocations"] == 0 and value["object_loader_invocations"] == 0
                and value["compile_credit"] is False and value["kernel_credit"] is False,
                "Fresh/original native qualification scope differs")
        reference = value["original_to_current_imports"]
        require(reference["path"] in environment.files
                and reference["sha256"] == environment.files[reference["path"]]["sha256"]
                and json_value(Path(reference["path"]).read_bytes()) == table,
                "Qualification import table is not exactly frozen")
        value["original_to_current_imports"]["sha256"] = "VERIFIED_EQUIVALENT_IMPORT_TABLE"
        return normalize(value, environment.path.parent)

    def compare_environments(self):
        old, new = self.old, self.external
        require(set(new.modules) == set(NATIVE_MODULES) and set(new.value) == set(old.value)
                and new.value["packages"] == old.value["packages"]
                and new.value["caller_scope"] == old.value["caller_scope"], "Native package/caller scope changed")
        require(normalize(old.value["runtime"], old.path.parent) == normalize(new.value["runtime"], new.path.parent),
                "Runtime or search-root context changed")
        require(self.facets(old) == self.facets(new), "Actual resolved import facet contents changed")
        direct_external = {dep for node in self.protected.values()
                           for dep in parser_module.imports(node["source"].read_text()) if not dep.startswith("ImbalancedChen.")}
        require(direct_external <= set(old.value["resolutions"]),
                "Original project import has no historical snapshot facet binding: "
                + ", ".join(sorted(direct_external - set(old.value["resolutions"]))))
        for name in NATIVE_MODULES:
            for key in ("package", "source", "imports", "git_blob_sha1"):
                require(old.modules[name][key] == new.modules[name][key], "Native source/import identity changed")
        new_scope = self.bound_json(new, "current-p27-scope")
        require(new_scope["project_modules"] == self.current_rows, "Fresh source census is not current")
        expected_scope = copy.deepcopy(self.scope)
        expected_scope["project_modules"] = self.current_rows
        require(normalize(expected_scope, old.path.parent) == normalize(new_scope, new.path.parent),
                "Fresh source scope changed beyond caller bytes")
        old_table, new_table = self.import_table(old), self.import_table(new)
        require(normalize(old_table, old.path.parent) == normalize(new_table, new.path.parent),
                "Original/actual import table changed beyond verified view locations")
        require(self.provider_context(old, old_table) == self.provider_context(new, new_table),
                "Native provider evidence changed beyond actual import rebinding")
        require(self.qualification(old, old_table) == self.qualification(new, new_table),
                "Native qualification history/base differs")
        old_files = normalize(old.files, old.path.parent)
        new_files = normalize(new.files, new.path.parent)
        require(set(old_files) == set(new_files), "New environment adds/removes unreviewed physical bindings")
        changed_paths = {value["source"] for value in self.changed.values()}
        for path, original in old_files.items():
            current = new_files[path]
            require(original.get("role") == current.get("role"), "Physical binding role changed")
            if (path.startswith("@p27-native-attempt/") and original.get("role") in METADATA_ROLES) or path in changed_paths:
                continue
            require(original == current, "External physical content changed beyond permitted caller metadata")

    def verify_current_dependencies(self):
        remaining = {n: v for n, v in self.protected.items() if n not in REBOUND_MODULES}
        require(all(set(node["deps"]) <= set(remaining) for node in remaining.values()), "Non-target dependency context is not closed")
        verify_compilation(self.records, remaining, self.frozen(self.new_binding))
        for name in MODULES:
            current, original = self.records.get(name, {}), self.original_records[name]
            require(current.get("exit_code") == 0 and all(current.get(k) == original[k] for k in
                    ("module", "source", "source_sha256", "object", "object_sha256", "deps", "toolchain")),
                    "Live target record differs from original actual input/output identity")
        record = self.records[CURRENTCHEN]
        reference = record.get("historical_cache_qualification", {})
        require(set(reference) == {"path", "sha256"}, "CurrentChen lacks its fresh adoption receipt")
        path = Path(reference["path"])
        require(path.resolve().is_relative_to(self.project) and path.is_file(), "CurrentChen receipt is outside this project")
        self.bind(path, "fresh-currentchen-adoption", reference["sha256"])
        receipt = json_value(path.read_bytes())
        require(receipt["schema"] == "p27-currentchen-historical-project-adoption-v1"
                and receipt["status"] == "EXACT_SOURCE_IMPORT_RUNTIME_REBIND_ONLY" and receipt["module"] == CURRENTCHEN
                and receipt["external_before"] == receipt["external_after"] == self.new_binding
                and receipt["closure_signature"] == record["closure_signature"]
                and receipt["source_sha256"] == self.original_records[CURRENTCHEN]["source_sha256"]
                and receipt["object_sha256"] == self.original_records[CURRENTCHEN]["object_sha256"]
                and record["new_strict_compile"] is False and receipt["new_strict_compile_credit"] is False
                and receipt["source_compiler_invocations"] == 0 and receipt["object_loader_invocations"] == 0
                and receipt["kernel_credit"] is False, "CurrentChen receipt is not the fresh exact-byte adoption")
        physical = receipt["physical_inputs"]
        for text, row in physical.items():
            self.bind(Path(text), "fresh-currentchen-adoption-input", row["sha256"], row["bytes"])
        for path in (self.project / source_relative(CURRENTCHEN), Path(record["object"]), self.external.path,
                     self.project / "verification/part2/adopt_p27_currentchen_cache.py"):
            require(str(path.resolve()) in physical, "Fresh CurrentChen adoption omits a mandatory bound input")
        self.adoption_reference = reference

    def final_recheck(self):
        self.recheck()
        self.verify_old_files()
        require(self.project_files() == self.project_snapshot, "Protected project files changed before publication")
        require(self.external.verify() == self.new_binding, "Fresh native environment changed before publication")
        ExternalSnapshot.verify_resolutions(self.old)
        # Re-evaluate absence too: newly appearing private/IR facets are not in
        # an existing hash inventory and must not escape the final check.
        require(self.facets(self.old) == self.facets(self.external), "Late imported facet changed")
        require(git(Path(MATHLIB), "rev-parse", "HEAD").decode().strip() == PIN, "Mathlib moved before publication")
        require(not self.registry.is_symlink() and self.registry.read_bytes() == self.registry_raw,
                "Another writer changed the registry")


def publish_transaction(registry: Path, before: bytes, out: Path, evidence: dict[str, bytes], after: bytes,
                        *, final_check=None) -> None:
    """One registry replace, no partially updated rows; own staging only."""
    require(not registry.is_symlink() and registry.read_bytes() == before, "Concurrent registry writer; nothing replaced")
    require(not out.exists() and not out.is_symlink(), "Output directory already exists")
    temporary = registry.with_suffix(".p27-unchanged-native-records.tmp")
    require(not temporary.exists() and not temporary.is_symlink(), "Earlier registry transaction needs diagnosis")
    created = []
    made_directory = False
    try:
        out.mkdir(parents=True, exist_ok=False)
        made_directory = True
        for name, data in evidence.items():
            require(Path(name).name == name, "Unsafe transaction evidence filename")
            path = out / name
            write_exclusive(path, data)
            created.append(path)
        write_exclusive(temporary, after)
        created.append(temporary)
        if final_check is not None:
            final_check()
        require(not registry.is_symlink() and registry.read_bytes() == before,
                "Concurrent registry writer during preparation; nothing replaced")
        temporary.replace(registry)
        created.remove(temporary)
    except BaseException:
        # Only these newly created transaction files belong to this invocation.
        for path in reversed(created):
            path.unlink(missing_ok=True)
        if made_directory:
            out.rmdir()
        raise


def rebind(args) -> dict:
    context = Context(args)
    records = copy.deepcopy(context.records)
    for name in context.protected:  # project_nodes inserts in dependency order.
        if name not in REBOUND_MODULES:
            continue
        original = context.original_records[name]
        node = context.protected[name]
        record = {key: copy.deepcopy(original[key]) for key in
                  ("module", "source", "source_sha256", "object", "object_sha256", "toolchain", "deps")}
        record.update(CREDITS)
        record.update(cache_schema=3, exit_code=0,
                      dependency_signatures={d: records[d]["closure_signature"] for d in node["deps"]},
                      external_snapshot=context.new_binding,
                      external_check={"status": "PASSED_BATCH_PRE_POST", "before": context.new_binding, "after": context.new_binding},
                      provenance="Original d734 strict compilation; verified unchanged inputs rebound to a fresh caller snapshot")
        record["closure_signature"] = closure_signature(record)
        records[name] = record
    require({n: v for n, v in records.items() if n not in REBOUND_MODULES}
            == {n: v for n, v in context.records.items() if n not in REBOUND_MODULES}, "Non-target registry entry would change")
    verify_compilation(records, context.protected, context.frozen(context.new_binding))
    receipt = {"schema": "p27-three-original-native-record-rebind-v1", "status": "EQUIVALENCE_VERIFIED_FOR_REGISTRY_CAS",
               "registry_publication": "Prepared evidence only; current records must reference this exact receipt and proposed signatures.",
               "original_job": ORIGINAL_JOB, "original_commit": ORIGINAL_COMMIT,
               "original_registry": {"path": str(context.out / "ORIGINAL_RECORDS.json"), "sha256": sha(context.original_raw),
                                     "external_anchor": args.original_records_sha256},
               "original_snapshot": {"path": str(context.out / "ORIGINAL_EXTERNAL_SNAPSHOT.json"), "sha256": ORIGINAL_SNAPSHOT_SHA},
               "original_capture_manifest": {"path": str(context.out / "ORIGINAL_CAPTURE.json"),
                                             "sha256": args.capture_manifest_sha256},
               "old_binding_historical_only": context.old_binding, "fresh_binding": context.new_binding,
               "modules": list(MODULES), "retained": list(RETAINED_MODULES), "rebound": list(REBOUND_MODULES),
               "protected_project_count": len(context.protected),
               "protected_project_inputs": context.project_snapshot, "changed_callers": context.changed,
               "currentchen_adoption": context.adoption_reference,
               "proposed_closure_signatures": {n: records[n]["closure_signature"] for n in REBOUND_MODULES},
               "original_registry_cas_sha256": sha(context.registry_raw),
               "physical_input_count": len(context.bound), "physical_input_manifest_sha256": signature(context.bound),
               "historical_snapshot_current_valid_claimed": False, "numeric_records_modified": False,
               "audit_files_modified": False, "objects_modified": False,
               "rebind_helper_sha256": sha(Path(__file__).read_bytes()), **CREDITS}
    receipt_raw = encoded(receipt)
    reference = {"path": str(context.out / "RECORD_REBIND.json"), "sha256": sha(receipt_raw)}
    for name in REBOUND_MODULES:
        records[name]["historical_cache_qualification"] = reference
    verify_compilation(records, context.protected, context.frozen(context.new_binding))
    context.final_recheck()
    verify_compilation(records, context.protected, context.frozen(context.new_binding))
    evidence = {"ORIGINAL_RECORDS.json": context.original_raw, "ORIGINAL_CAPTURE.json": context.capture_manifest["raw"],
                "ORIGINAL_EXTERNAL_SNAPSHOT.json": context.old.raw, "RECORD_REBIND.json": receipt_raw, **context.log_payloads}
    publish_transaction(context.registry, context.registry_raw, context.out, evidence, encoded(records),
                        final_check=context.final_recheck)
    return {"status": "TWO_NATIVE_RECORDS_REBOUND_ONE_NUMERIC_RETAINED", "modules": list(MODULES),
            "rebound": list(REBOUND_MODULES), "retained": list(RETAINED_MODULES),
            "receipt": reference, "original_registry_sha256": sha(context.original_raw), **CREDITS}


def capture(args) -> dict:
    context = Context(args, capture=True)
    log_inventory, log_payloads = context.compile_log_inventory(original_capture=True)
    context.final_recheck()
    metadata = {"schema": "p27-d734-original-registry-capture-v1", "status": "ORIGINAL_BYTES_CAPTURED_NOT_MIGRATED",
                "original_job": ORIGINAL_JOB, "head": ORIGINAL_COMMIT, "project": str(context.project),
                "registry_sha256": sha(context.registry_raw), "registry_bytes": len(context.registry_raw),
                "snapshot_sha256": ORIGINAL_SNAPSHOT_SHA, "original_strict_modules": list(MODULES),
                "compile_logs": log_inventory,
                "log_hash_boundary": "Hashes observed during capture; original compiler records did not contain log hashes.",
                "capture_helper_sha256": sha(Path(__file__).read_bytes()), **CREDITS}
    created = []
    made_directory = False
    try:
        context.out.mkdir(parents=True, exist_ok=False)
        made_directory = True
        for name, data in {"records.json": context.registry_raw, "EXTERNAL_SNAPSHOT.json": context.old.raw,
                           "CAPTURE.json": encoded(metadata), **log_payloads}.items():
            path = context.out / name
            write_exclusive(path, data)
            created.append(path)
        context.final_recheck()
        require(git(context.project, "rev-parse", "HEAD").decode().strip() == ORIGINAL_COMMIT,
                "Project HEAD changed during original capture")
    except BaseException:
        for path in reversed(created):
            path.unlink(missing_ok=True)
        if made_directory:
            context.out.rmdir()
        raise
    return {**metadata, "original_records": str(context.out / "records.json"),
            "capture_manifest_sha256": sha(encoded(metadata)),
            "instruction": "Independently retain/verify this stdout SHA before using it as --original-records-sha256."}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("capture", "rebind"):
        sub = commands.add_parser(name)
        sub.add_argument("--project-root", type=Path, required=True)
        sub.add_argument("--original-snapshot", type=Path, required=True)
        sub.add_argument("--out", type=Path, required=True)
        if name == "rebind":
            sub.add_argument("--original-records", type=Path, required=True)
            sub.add_argument("--original-records-sha256", required=True)
            sub.add_argument("--capture-manifest-sha256", required=True)
            sub.add_argument("--external-snapshot", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = capture(args) if args.command == "capture" else rebind(args)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(json.dumps({"status": "ORIGINAL_RECORD_REBIND_BLOCKED", "reason": str(error), **CREDITS}), flush=True)
        return 2
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
