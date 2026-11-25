#!/usr/bin/env python3
"""Rebind the one existing P6 CurrentChen object to a qualified P2.7 environment.

This is a single-module historical-cache receiver, not a Winner9 request or a
native qualifier. Its output is a schema-3 historical record with no new strict
compile/kernel credit. Independent replay and owned-declaration/axiom audits
remain mandatory. Run only when the private registry's compiler writer is idle.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
import p27_qualify_native_inputs as inputs
from p27_qualify_native_inputs import (InputBindings, NativeTransfer, P27Qualification,
                                     P6_ROOT, TAIL, MATHLIB_PIN, module_path, write_new)
from qualify_winner9_native_cache import atomic_missing, LOAD_SUFFIXES, PROTOCOL, PROTOCOL_SHA256
from run_winner9_private_checks import EXTERNAL_CACHE_SCHEMA, LEAN, closure_signature, digest
from run_winner9_private_audit import project_nodes, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, native, require, signature

MODULE = "ImbalancedChen.CurrentChenBuchstabRefinement"
SOURCE_SHA = "02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5"
OBJECT_SHA = "4eb6075c0bcda6ee6d8773fa93c97347b3d727146c944315c1f0d89de498f652"
INDEX_SHA = "dd84c936cf1d95a49407849241e4e18369842d427a0ee97dd2f6bf55e8528799"
INDEX_REPO_PATH = "docs/verification/20261123-blue-compilation/p6-four-roots/ALL_SELECTED_PROJECT_SOURCE_AND_FACETS_BEFORE.json"
FOUR = "/workspace/blue-p6-controller/final-four-roots"
P6_SHADOW = "/workspace/blue-build-tools/runtime/p0-ci-shadow-toolchain"
RUNTIME_STATE = "/workspace/blue-build-tools/runtime-evidence/state.json"
RUNTIME_STATE_SHA = "e474b9cb4b9e4d9cc4cc0c3ba58b29b0096f1bdec6f104d2e41a17f521ca232b"
RUNTIME_LOG = "/workspace/blue-build-tools/runtime-evidence/compiler-commands.jsonl"
RUNTIME_LOG_SHA = "a5a4a446dc0ce049cffb4afc518a1d2a5c308a966a9a31a4506d5c136bc1072b"
ORIGINAL_MAP_SHA = "1c9e2dfa009b62d9ab0e6a3f8dd089b69564b1febb14c41efae56317eb87e140"
OLD_SOURCE = P6_ROOT + "/" + module_path(MODULE) + ".lean"
OLD_LIB_STEM = P6_ROOT + "/.lake/build/lib/lean/" + module_path(MODULE)
OLD_IR_STEM = P6_ROOT + "/.lake/build/ir/" + module_path(MODULE)
ORIGINAL_INPUT_ARGS = [OLD_SOURCE, "-o", OLD_LIB_STEM + ".olean", "-i", OLD_LIB_STEM + ".ilean",
                       "-c", OLD_IR_STEM + ".c", "--setup", OLD_IR_STEM + ".setup.json", "--json"]
OPTIONS = {"maxRecDepth": "100000", "maxHeartbeats": "4000000"}
FOUR_ANCHORS = {
    "FOUR_ROOT_ACCEPTANCE.json": ("45fc9c91fe43a3a2aec2bad74562812adcacaa5411b3cf9a8e2661fd1dbed22f", 13533),
    "STOCK_PROCESS.json": ("82fe288f815061a6269efc0c0c28d64ee6122cf9066913331073301589780095", 743),
    "STOCK_GUARD_COMMANDS.jsonl": ("95743689671d6ea63243391a7599846eb031bd32413d660fd40aaed332128416", 321),
    "stock.log": ("23345131900a5f0c6ed5b6a19fd8e090b24579a977298d15291ed3770a8acf86", 211128),
}


def normalize_d_options(arguments: list[str]) -> tuple[dict, list[str]]:
    options, remaining, index = {}, [], 0
    while index < len(arguments):
        token = arguments[index]
        if token == "-D":
            index += 1
            require(index < len(arguments), "Incomplete original -D option")
            option = arguments[index]
        elif token.startswith("-D"):
            option = token[2:]
        else:
            remaining.append(token)
            index += 1
            continue
        require("=" in option, "Malformed original -D option")
        key, value = option.split("=", 1)
        require(key not in options, "Duplicate original -D option")
        options[key] = value
        index += 1
    return options, remaining


def validate_source_event(event: dict) -> dict:
    require(event["tool"] == "lean" and event["cwd"] == P6_ROOT and event["sysroot"] == P6_SHADOW
            and event["command"][0] == P6_SHADOW + "/bin/lean-runtime", "Wrong original P6 source event")
    require(event["command"][1:4] == ["-t0", "-j2", "-M12288"], "Original source event is not the fixed trust-zero profile")
    command_options, command_args = normalize_d_options(event["command"][4:])
    input_options, input_args = normalize_d_options(event["input_args"])
    require(command_options == input_options == OPTIONS, "Original project option normalization differs")
    require(command_args == input_args == ORIGINAL_INPUT_ARGS, "Original source/output arguments differ")
    return {"options": command_options, "arguments": command_args}


def validate_index_pair(before: bytes, after: bytes) -> dict:
    require(before == after and len(before) == 333730 and hashlib.sha256(before).hexdigest() == INDEX_SHA,
            "The complete original project index differs")
    value = json.loads(before)
    require(len(value) == 208 and MODULE in value, "Original project index scope differs")
    row = value[MODULE]
    require(row["source"] == {"path": OLD_SOURCE, "bytes": 6536, "sha256": SOURCE_SHA}
            and row["selected_source_sha256"] == SOURCE_SHA
            and row["facets"]["olean"] == {"path": OLD_LIB_STEM + ".olean", "bytes": 570136, "sha256": OBJECT_SHA},
            "Original single-module source/output identity differs")
    return row


def reject_extra_project_facets(lib: Path) -> None:
    stem = lib / module_path(MODULE)
    for suffix in LOAD_SUFFIXES:
        path = Path(str(stem) + suffix)
        if suffix != ".olean":
            require(not path.exists() and not path.is_symlink(), "Extra unqualified project facet: " + str(path))


def install_project_object(lib: Path, candidate: Path, expected: str) -> Path:
    reject_extra_project_facets(lib)
    target = lib / (module_path(MODULE) + ".olean")
    require(target.resolve().is_relative_to(lib.resolve()), "Project object escapes its private library")
    require(not target.is_symlink(), "Existing project object is a symlink")
    require(not target.exists() or (target.is_file() and digest(target) == expected),
            "An existing different project object must be retained")
    atomic_missing(target, candidate.read_bytes(), expected)
    return target


def make_record(project: Path, source: Path, obj: Path, toolchain: dict, external: dict) -> dict:
    record = {"module": MODULE, "source": str(source.relative_to(project)), "source_sha256": digest(source),
              "object": str(obj), "object_sha256": digest(obj), "exit_code": 0,
              "deps": {}, "dependency_signatures": {}, "cache_schema": EXTERNAL_CACHE_SCHEMA,
              "toolchain": toolchain, "new_strict_compile": False, "kernel_credit": False,
              "provenance": "Existing guarded P6 CurrentChen object; exact current source/import/runtime rebind",
              "external_snapshot": external,
              "external_check": {"status": "PASSED_BATCH_PRE_POST", "before": external, "after": external}}
    record["closure_signature"] = closure_signature(record)
    return record


def commit_record(path: Path, original_raw: bytes | None, records: dict) -> None:
    require(not path.is_symlink(), "Private compile registry is a symlink")
    require((path.read_bytes() if path.exists() else None) == original_raw,
            "Another writer changed the compile registry; no records were replaced")
    temporary = path.with_suffix(".p27-currentchen-adoption.tmp")
    require(not temporary.exists(), "An earlier project-cache transaction needs diagnosis")
    write_new(temporary, records)
    # Repeat immediately before replacement, following the existing receiver's
    # registry ownership rule. The caller must schedule this with writers idle.
    require((path.read_bytes() if path.exists() else None) == original_raw,
            "Another writer changed the compile registry during preparation")
    temporary.replace(path)


class CurrentChenReceiver(InputBindings):
    def __init__(self, args) -> None:
        self.project = args.project_root.resolve(strict=True)
        self.private_lib = self.project / ".lake/p2-private/lib"
        require(self.private_lib.resolve().is_relative_to(self.project), "Private library points outside isolated project")
        self.external = ExternalSnapshot(args.external_snapshot, lean=LEAN, mathlib_pin=MATHLIB_PIN,
                                         project_lib=self.private_lib)
        super().__init__(self.external.hashes)
        self.before = self.external.binding()
        self.out = args.out.resolve()
        require(not self.out.exists() and self.out.is_relative_to(self.project)
                and not self.out.is_relative_to(self.private_lib.resolve())
                and not self.out.is_relative_to(self.external.path.parent)
                and not self.out.is_relative_to(args.project_bundle.resolve())
                and not self.out.is_relative_to(args.native_bundle.resolve())
                and all(not self.out.is_relative_to(Path(row["root"]).resolve())
                        for row in self.external.value["packages"].values()),
                "Use a new isolated project-adoption evidence directory")
        self.out.mkdir(parents=True)
        self.bundle = NativeTransfer(args.project_bundle, self.hashes)
        self.native_bundle = NativeTransfer(args.native_bundle, self.hashes)
        for bundle in (self.bundle, self.native_bundle):
            self.bind(bundle.manifest_path, "transport-only-manifest", bundle.manifest_sha)
        manifest = json.loads(self.bundle.manifest_path.read_text())
        require(manifest.get("scope") == "existing_project_module_object" and set(manifest["modules"]) == {MODULE},
                "Project transport is not the single CurrentChen scope")
        self.bind(self.external.path, "qualified-native-snapshot", self.external.raw_sha256)
        self.nodes = project_nodes(self.project, MODULE)
        require(set(self.nodes) == {MODULE} and self.nodes[MODULE]["deps"] == [], "Unexpected project dependencies")
        self.nodes[MODULE]["package"] = "imbalancedChen"
        self.source = self.nodes[MODULE]["source"]
        self.bind(self.source, "current-exact-project-source", SOURCE_SHA, 6536)
        require(inputs.source_imports(self.source.read_text())[0] == TAIL, "Expected native source ancestry changed")
        self.bind(PROTOCOL, "original-descriptor-validator", PROTOCOL_SHA256)
        spec = importlib.util.spec_from_file_location("currentchen_original_descriptor_protocol", PROTOCOL)
        require(spec is not None and spec.loader is not None, "Cannot load original descriptor validator")
        self.protocol = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.protocol)
        for path in (Path(__file__), Path(inputs.__file__), Path(sys.modules["run_winner9_private_checks"].__file__),
                     Path(sys.modules["run_winner9_private_audit"].__file__),
                     Path(sys.modules["winner9_external_snapshot"].__file__)):
            self.bind(path, "receiver-tool")
        self.toolchain = {"lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
                          "lean_binary_sha256": self.hashes.digest(Path(LEAN)), "mathlib_commit": MATHLIB_PIN}
        self.registry = self.project / ".lake/p2-private/records.json"
        require(not self.registry.is_symlink(), "Private compile registry is a symlink")
        self.original_raw = self.registry.read_bytes() if self.registry.exists() else None
        self.records = json.loads(self.original_raw) if self.original_raw else {}

    def supplied(self, bundle: NativeTransfer, original: str, sha: str, size: int | None = None) -> Path:
        path = bundle.get(original, sha, size)
        self.bind(path, "original-supplier-payload", sha, size)
        return path

    def transport(self, original: str, sha: str, size: int | None = None) -> Path:
        # The shared metadata checker only locates and hashes original bytes.
        # It does not instantiate or alter either native caller's scope.
        return self.supplied(self.bundle, original, sha, size)

    def historical_context(self) -> tuple[dict, dict]:
        indices = [self.transport(FOUR + "/ALL_SELECTED_PROJECT_SOURCE_AND_FACETS_" + suffix + ".json", INDEX_SHA, 333730)
                   for suffix in ("BEFORE", "AFTER")]
        row = validate_index_pair(*(p.read_bytes() for p in indices))
        records = {name: self.transport(FOUR + "/" + name, sha, size)
                   for name, (sha, size) in FOUR_ANCHORS.items()}
        acceptance = json.loads(records["FOUR_ROOT_ACCEPTANCE.json"].read_text())
        stock = json.loads(records["STOCK_PROCESS.json"].read_text())
        require(acceptance["project"] == P6_ROOT and acceptance["final_stock_source_and_facet_snapshots_unchanged"] is True
                and acceptance["native_or_project_cache_reuse_is_new_proof_work"] is False
                and acceptance["final_stock"] == stock and stock["exit_code"] == 0 and stock["source_compiler_calls"] == 0
                and stock["log_sha256"] == FOUR_ANCHORS["stock.log"][0], "Original P6 stock/source context differs")
        require(MODULE not in acceptance["project_postimage_modules"]
                and all(MODULE not in phase["declared_audit_scope"] for phase in acceptance["phases"].values()),
                "Unexpected historical source/audit scope")
        original_source = self.transport(row["source"]["path"], SOURCE_SHA, 6536)
        require(original_source.read_bytes() == self.source.read_bytes(), "Current source is not the original compiled source")
        facets = [{"original_path": v["path"], "sha256": v["sha256"], "bytes": v["bytes"]}
                  for v in row["facets"].values()]
        # Sidecars are current observed bytes checked against the independently
        # anchored original trace descriptors, not newly invented old SHA facts.
        for key in ("olean", "ilean", "c"):
            original = row["facets"][key]["path"] + ".hash"
            require(original in self.bundle.files, "Missing original descriptor sidecar")
            v = self.bundle.files[original]
            facets.append({"original_path": original, "sha256": v["sha256"], "bytes": v["bytes"]})
        setup, loadable, metadata = P27Qualification.metadata(self, MODULE, facets, P6_ROOT)
        require(setup["isModule"] is False and set(loadable) == {".olean"}, "Unexpected original project module/facet mode")
        trace_copy = self.out / "original-trace.json"
        atomic_missing(trace_copy, Path(metadata["trace"]).read_bytes(), row["facets"]["trace"]["sha256"])
        self.bind(trace_copy, "original-trace-text-copy", row["facets"]["trace"]["sha256"])
        metadata["original_trace_text_copy"] = str(trace_copy)
        for suffix in LOAD_SUFFIXES:
            require(suffix == ".olean" or OLD_LIB_STEM + suffix not in self.bundle.files,
                    "Unanchored extra project loadable facet in transport")
        return {"index_paths": list(map(str, indices)), "index_sha256": INDEX_SHA,
                "four_root_records": {n: str(p) for n, p in records.items()},
                "prior_named_currentchen_audit_claimed": False, "metadata": metadata,
                "sidecar_sha_history_claimed": False}, {"setup": setup, "candidate": loadable[".olean"]}

    def runtime_context(self) -> dict:
        state_path = self.supplied(self.native_bundle, RUNTIME_STATE, RUNTIME_STATE_SHA, 4391)
        log_path = self.supplied(self.native_bundle, RUNTIME_LOG, RUNTIME_LOG_SHA, 2058624)
        state = json.loads(state_path.read_text())
        require(state["shadow"] == P6_SHADOW and state["log"] == RUNTIME_LOG, "Original P6 runtime coordinates changed")
        wrappers = {state["shadow"] + "/bin/" + name for name in state["tools"]}
        payloads = {p: sha for p, sha in state["runtime_sha256"].items() if p not in wrappers}
        require(len(payloads) == 11, "Original P6 runtime payload census differs")
        runtime_bindings = []
        sysroot = Path(self.external.value["runtime"]["sysroot"])
        for original, sha in payloads.items():
            name = Path(original).name
            current = (sysroot / "bin" / ("lean" if name == "lean-runtime" else name)).resolve(strict=True)
            require(str(current) in self.external.files and self.external.files[str(current)]["sha256"] == sha,
                    "Original P6 runtime is not the qualified current runtime")
            self.bind(current, "original-runtime-rebound", sha)
            runtime_bindings.append({"original": original, "current": str(current), "sha256": sha})
        events = [json.loads(line) for line in log_path.read_text().splitlines() if OLD_SOURCE in line]
        events = [e for e in events if e.get("tool") == "lean" and OLD_SOURCE in e.get("input_args", [])]
        require(len(events) == 1, "Missing/ambiguous original CurrentChen source event")
        normalized = validate_source_event(events[0])
        return {"state": str(state_path), "compiler_log": str(log_path), "source_event": events[0],
                "normalized_project_options": normalized, "runtime_policy": state["policy"], "runtime_bindings": runtime_bindings}

    def imports_context(self, setup: dict) -> dict:
        receipt_path = self.supplied(self.native_bundle, inputs.P6_RECEIPT, inputs.P6_RECEIPT_SHA, inputs.P6_RECEIPT_BYTES)
        receipt = json.loads(receipt_path.read_text())
        rows = inputs.p6_recheck_table(receipt["actual_import_rechecks"], inputs.P6_RECHECK_COUNT, inputs.P6_RECHECK_SHA)
        own = [f for f in receipt["installed_files"] if f["relative_path"] == ".lake/build/lib/lean/" + module_path(TAIL) + ".olean"]
        require(len(own) == 1 and own[0]["sha256"] == inputs.P6_OBJECT_SHA, "Anchored native Tail object differs")
        old_tail = P6_ROOT + "/.lake/packages/goldbach/" + own[0]["relative_path"]
        rows[old_tail] = {"module": TAIL, "sha256": own[0]["sha256"], "bytes": own[0]["bytes"]}
        original = inputs.p6_setup_map(setup, P6_ROOT, rows)
        require(signature(original) == ORIGINAL_MAP_SHA, "Original CurrentChen actual-import map differs")
        current = {}
        for name, parts in original.items():
            require(not name.startswith("ImbalancedChen."), "Unexpected actual project import")
            require(name in self.external.value["resolutions"], "Current input is absent from qualified native environment: " + name)
            if native(name):
                require(name in self.external.modules, "Actual native input lacks its own provider")
            obj = self.external.value["resolutions"][name]
            require(obj.endswith(".olean"), "Malformed qualified public object")
            current[name] = []
            for old, sha in parts:
                stem = name.rsplit(".", 1)[-1]
                require(Path(old).name.startswith(stem + "."), "Original imported facet has another module stem")
                suffix = Path(old).name[len(stem):]
                require(suffix in LOAD_SUFFIXES, "Unexpected actual imported facet")
                path = Path(obj[:-len(".olean")] + suffix).resolve(strict=True)
                require(str(path) in self.external.files and self.external.files[str(path)]["sha256"] == sha,
                        "Original input is not byte-exact in current qualified environment: " + old)
                self.bind(path, "actual-import-rebound", sha)
                current[name].append([str(path), sha])
        path = self.out / "ACTUAL_IMPORT_REBIND.json"
        write_new(path, {"original": original, "current": current, "source": str(receipt_path),
                         "original_sha256": signature(original), "current_sha256": signature(current),
                         "grouping": "Read the anchored original setup to preserve subgroup boundaries and order."})
        self.bind(path, "actual-import-rebinding")
        return {"path": str(path), "sha256": self.hashes.digest(path), "modules": len(original),
                "facets": sum(map(len, original.values())), "original_map_sha256": signature(original),
                "current_map_sha256": signature(current)}

    def frozen_project(self, obj: Path) -> dict:
        return {"project": {MODULE: {"source": str(self.source.relative_to(self.project)),
                                      "source_sha256": self.hashes.digest(self.source), "object": str(obj),
                                      "object_sha256": self.hashes.digest(obj)}},
                "toolchain": self.toolchain, "lean_binary_sha256": self.hashes.digest(Path(LEAN)),
                "external_snapshot": self.before}

    def run(self) -> int:
        reject_extra_project_facets(self.private_lib)
        obj = self.private_lib / (module_path(MODULE) + ".olean")
        try:
            verify_compilation(self.records, self.nodes, self.frozen_project(obj))
        except (OSError, ValueError, KeyError):
            pass
        else:
            print(json.dumps({"status": "CURRENT_VALID_RECORD_RETAINED", "module": MODULE,
                              "source_compiler_invocations": 0, "kernel_credit": False}), flush=True)
            return 0
        history, candidate = self.historical_context()
        runtime = self.runtime_context()
        imports = self.imports_context(candidate["setup"])
        self.recheck()
        require(self.external.verify() == self.before, "Native environment changed before project installation")
        obj = install_project_object(self.private_lib, candidate["candidate"], OBJECT_SHA)
        self.bind(obj, "historical-project-object", OBJECT_SHA, 570136)
        after = self.external.verify()
        require(after == self.before, "Native environment changed during project adoption")
        self.recheck()
        record = make_record(self.project, self.source, obj, self.toolchain, self.before)
        records = copy.deepcopy(self.records)
        records[MODULE] = record
        verify_compilation(records, self.nodes, self.frozen_project(obj))
        receipt = {"schema": "p27-currentchen-historical-project-adoption-v1", "status": "EXACT_SOURCE_IMPORT_RUNTIME_REBIND_ONLY",
                   "module": MODULE, "source_sha256": SOURCE_SHA, "object_sha256": OBJECT_SHA,
                   "history": history, "runtime": runtime, "actual_imports": imports,
                   "external_before": self.before, "external_after": after,
                   "original_registry_sha256": hashlib.sha256(self.original_raw).hexdigest() if self.original_raw else None,
                   "previous_record": self.records.get(MODULE), "closure_signature": record["closure_signature"],
                   "source_compiler_invocations": 0, "object_loader_invocations": 0,
                   "runtime_version_queries": 1, "new_strict_compile_credit": False, "kernel_credit": False,
                   "independent_currentchen_audit_claimed": False, "physical_inputs": self.bound}
        path = self.out / "PROJECT_CACHE_ADOPTION.json"
        write_new(path, receipt)
        record["historical_cache_qualification"] = {"path": str(path), "sha256": self.hashes.digest(path)}
        self.bind(path, "single-module-adoption-receipt")
        self.recheck()
        require(self.external.verify() == self.before, "Native environment changed before registry publication")
        # Recheck absent private/server/IR facets too; a late extra facet must
        # not evade the object SHA checks or become part of the accepted cache.
        install_project_object(self.private_lib, candidate["candidate"], OBJECT_SHA)
        verify_compilation(records, self.nodes, self.frozen_project(obj))
        commit_record(self.registry, self.original_raw, records)
        print(json.dumps({"status": receipt["status"], "module": MODULE, "receipt": str(path),
                          "cache_schema": EXTERNAL_CACHE_SCHEMA, "new_strict_compile": False,
                          "source_compiler_invocations": 0, "kernel_credit": False}), flush=True)
        return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--external-snapshot", type=Path, required=True)
    parser.add_argument("--native-bundle", type=Path, required=True)
    parser.add_argument("--project-bundle", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    existed = args.out.exists()
    try:
        return CurrentChenReceiver(args).run()
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        result = {"status": "CURRENTCHEN_CACHE_NOT_ADOPTED", "error": str(error),
                  "new_strict_compile_credit": False, "kernel_credit": False}
        path = args.out.resolve() / "FAILURE.json"
        if not existed and path.parent.is_dir() and not path.exists():
            write_new(path, result)
        print(json.dumps(result), flush=True)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
