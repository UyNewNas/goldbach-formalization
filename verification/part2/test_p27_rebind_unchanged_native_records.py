"""Narrow physical fixtures for the original d734 three-record rebind."""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import p27_rebind_unchanged_native_records as r
import winner9_external_snapshot as ext
from inspect_winner9_owner_native import imports as source_imports
from run_winner9_private_audit import project_nodes, verify_compilation
from run_winner9_private_checks import closure_signature, json_digest


def raw(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def sha(value):
    return hashlib.sha256(value).hexdigest()


def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data if isinstance(data, bytes) else data.encode())
    return path


def commit(path):
    for args in (["init", "-q"], ["add", "."], ["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"]):
        subprocess.run(["git", *args], cwd=path, check=True, capture_output=True)
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=path, text=True).strip()


class Fixture:
    """Real Git blobs, snapshot files/resolution and existing compilation validators."""
    def __init__(self, base, changed=True):
        self.root = base / "project"
        self.root.mkdir()
        self.lib = self.root / ".lake/p2-private/lib"
        self.lib.mkdir(parents=True)
        self.registry = self.root / ".lake/p2-private/records.json"
        self.old_dir = self.root / ".lake/p27-native/attempt-001"
        self.new_dir = self.root / ".lake/p27-native/attempt-002"
        self.old_path = self.old_dir / "EXTERNAL_SNAPSHOT.json"
        self.new_path = self.new_dir / "EXTERNAL_SNAPSHOT.json"
        self.sysroot = base / "toolchain"
        self.lean = put(self.sysroot / "bin/lean", "fixture compiler bytes")
        self.checker = put(self.sysroot / "bin/leanchecker", "fixture checker bytes")
        self.core = self.sysroot / "lib/lean"
        self.core.mkdir(parents=True)
        self.runtime_files = [self.lean, self.checker] + [put(self.sysroot / "bin" / ("abi" + str(i)), str(i)) for i in range(9)]
        self.mathlib = base / "mathlib"
        self.std_source = put(self.mathlib / "Mathlib/Fixture.lean", "def fixture := 0\n")
        self.mathlib_pin = commit(self.mathlib)
        self.std_lib = self.mathlib / ".lake/build/lib/lean"
        self.std_object = put(self.std_lib / "Mathlib/Fixture.olean", "standard object")
        self.std_ir = put(self.std_lib / "Mathlib/Fixture.ir", "standard ir")
        self.packages = {}
        self.native_sources = {}
        for package in ("goldbach", "LeanArchitect"):
            package_root = base / package
            package_root.mkdir()
            put(package_root / "README", package)
            if package == "goldbach":
                for index, name in enumerate(r.NATIVE_MODULES):
                    deps = ["Mathlib.Fixture", *r.NATIVE_MODULES[:index]]
                    self.native_sources[name] = put(package_root / (name.replace(".", "/") + ".lean"),
                                                    "".join("import " + d + "\n" for d in deps))
            self.packages[package] = {"root": str(package_root), "commit": commit(package_root)}
        self.numbers = ["ImbalancedChen.RebindFixtureN" + str(i) for i in range(9)]
        self.changed_name = "ImbalancedChen.P2PairedFibreBuchstabVariableLower"
        self.graph = {name: [self.numbers[index + 1]] if index + 1 < len(self.numbers) else []
                      for index, name in enumerate(self.numbers)}
        self.graph[r.CURRENTCHEN] = []
        self.graph[r.MODULES[0]] = [self.numbers[0]]
        self.graph[r.MODULES[1]] = [r.CURRENTCHEN, r.MODULES[0]]
        self.graph[r.MODULES[2]] = [self.numbers[0], r.CURRENTCHEN]
        self.graph[self.changed_name] = []
        fillers = ["ImbalancedChen.RebindFixtureCaller" + str(i) for i in range(66)]
        self.graph.update({name: [] for name in fillers})
        self.graph[r.ROOT] = [*r.MODULES, self.changed_name, *fillers]
        assert len(self.graph) == 81
        self.sources = {}
        for name, deps in self.graph.items():
            external = [r.NATIVE_MODULES[2]] if name == r.CURRENTCHEN else []
            self.sources[name] = put(self.root / (name.replace(".", "/") + ".lean"),
                                     "".join("import " + d + "\n" for d in [*deps, *external]) + "def value := 0\n")
        self.helper_paths = []
        for filename in r.FROZEN_HELPERS:
            actual = Path(r.__file__).with_name(filename)
            self.helper_paths.append(put(self.root / "verification/part2" / filename, actual.read_bytes()))
        put(self.root / ".gitignore", ".lake/\n")
        self.original_commit = commit(self.root)
        self.original_sources = {name: path.read_bytes() for name, path in self.sources.items()}
        self.common = [*self.runtime_files, self.std_source, self.std_object, self.std_ir,
                       *self.native_sources.values(), *self.helper_paths]
        self.original_base = put(base / "BASE_SNAPSHOT.json", raw({"fixture": "same immutable base"}))
        self.common.append(self.original_base)
        self.base_binding = {"snapshot": str(self.original_base), "snapshot_sha256": sha(self.original_base.read_bytes()),
                             "fixture": "same base in both normal qualifications"}
        self.setups = {}
        for i, name in enumerate(r.NATIVE_MODULES):
            arts = {"Mathlib.Fixture": [["/original/Mathlib/Fixture.olean", "/original/Mathlib/Fixture.ir"]]}
            arts.update({dep: [["/original/" + dep.replace(".", "/") + ".olean"]] for dep in r.NATIVE_MODULES[:i]})
            setup = {"name": name, "package": "goldbach", "importArts": arts}
            self.setups[name] = put(base / "original-setups" / (name + ".setup.json"), raw(setup))
            self.common.append(self.setups[name])
        self.old = self.environment(self.old_dir)
        self.old_sha = sha(self.old_path.read_bytes())
        self.toolchain = {"lean_version": "Lean (version fixture)", "lean_binary_sha256": sha(self.lean.read_bytes()),
                          "mathlib_commit": self.mathlib_pin}
        self.records = self.make_records(self.old_path, self.old)
        put(self.registry, raw(self.records))
        self.original_records_path = put(self.root / ".lake/p27-native-record-rebind/input-d734/records.json", raw(self.records))
        self.original_records_sha = sha(self.original_records_path.read_bytes())
        self.make_capture()
        self.audit = put(self.root / ".lake/p2-private/audit/already-accepted.json", raw({"accepted": "untouched"}))
        if changed:
            self.sources[self.changed_name].write_text("def value := 1\n")
        self.new = self.environment(self.new_dir)
        self.adopt_currentchen()
        self.current_before = self.registry.read_bytes()
        self.out = self.root / ".lake/p2-private/native-record-rebind/attempt-002"

    @staticmethod
    def identity(path, role):
        return {"sha256": sha(path.read_bytes()), "bytes": path.stat().st_size, "role": role}

    def source_row(self, name, path, package):
        data = path.read_bytes()
        return {"package": package, "source": str(path), "source_sha256": sha(data), "source_bytes": len(data),
                "git_blob_sha1": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
                "direct_imports": source_imports(data.decode())}

    def environment(self, directory):
        directory.mkdir(parents=True)
        files = {str(p): self.identity(p, "stable-input") for p in self.common}
        files[str(self.original_base)]["role"] = "native-qualification-receipt"
        files.update({str(p): self.identity(p, "current-project-source") for p in self.sources.values()})
        view = directory / "lib/lean"
        resolutions = {"Mathlib.Fixture": str(self.std_object)}
        for name in r.NATIVE_MODULES:
            obj = put(view / (name.replace(".", "/") + ".olean"), "native object " + name)
            files[str(obj)] = self.identity(obj, "qualified-native-artifact")
            resolutions[name] = str(obj)
        native_rows = {name: self.source_row(name, p, "goldbach") for name, p in self.native_sources.items()}
        projects = {name: self.source_row(name, p, "project") for name, p in self.sources.items()}
        scope = {"schema": "p27-actual-source-native-scope-v1", "roots": [r.ROOT], "project_root": str(self.root),
                 "project_modules": projects, "project_count": 81, "native_modules": native_rows, "native_count": 3,
                 "direct_native_entries": [r.NATIVE_MODULES[2]],
                 "base_snapshot": self.base_binding, "compile_credit": False, "kernel_credit": False}
        scope_path = put(directory / "SOURCE_SCOPE.json", raw(scope))
        files[str(scope_path)] = self.identity(scope_path, "current-p27-scope")
        bindings = {}
        for name, suffix, target in [("Mathlib.Fixture", ".olean", self.std_object), ("Mathlib.Fixture", ".ir", self.std_ir)]:
            bindings["/original/" + name.replace(".", "/") + suffix] = {
                "module": name, "current": str(target), "sha256": sha(target.read_bytes()), "bytes": target.stat().st_size}
        for name in r.NATIVE_MODULES[:2]:
            target = Path(resolutions[name])
            bindings["/original/" + name.replace(".", "/") + ".olean"] = {
                "module": name, "current": str(target), "sha256": sha(target.read_bytes()), "bytes": target.stat().st_size}
        table_path = put(directory / "ORIGINAL_TO_CURRENT_IMPORTS.json", raw({
            "schema": "p27-original-to-current-physical-imports-v1", "paths": bindings, "reconstruction": "fixture"}))
        files[str(table_path)] = self.identity(table_path, "actual-import-rebinding-table")
        qualified = {}
        for name in r.NATIVE_MODULES:
            setup = json.loads(self.setups[name].read_bytes())
            original = {module: [[p, bindings[p]["sha256"]] for group in groups for p in group]
                        for module, groups in setup["importArts"].items()}
            current = {module: [[bindings[p]["current"], digest] for p, digest in parts] for module, parts in original.items()}
            provider = {"schema": "p27-existing-native-provider-rebind-v1", "status": "EXACT_ORIGINAL_IMPORTS_REBOUND",
                        "module": name, "source": str(self.native_sources[name]), "source_sha256": native_rows[name]["source_sha256"],
                        "objects": {resolutions[name]: files[resolutions[name]]}, "setup": str(self.setups[name]),
                        "source_runtime_event": {"cwd": "/original"},
                        "original_import_map_sha256": ext.signature(original), "actual_import_map_sha256": ext.signature(current),
                        "new_source_compilation": False, "compile_credit": False, "kernel_credit": False}
            pp = put(directory / "providers" / (name + ".json"), raw(provider))
            files[str(pp)] = self.identity(pp, "native-provider-receipt")
            qualified[name] = {"status": "EXACT_ORIGINAL_IMPORTS_REBOUND", "receipt": str(pp)}
        qualification = {"schema": "p27-native-input-qualification-v1", "status": "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED",
                         "roots": [r.ROOT], "project_count": 81, "native_count": 3, "qualified": qualified, "blocked": {},
                         "base_snapshot": self.base_binding,
                         "original_to_current_imports": {"path": str(table_path), "sha256": sha(table_path.read_bytes())},
                         "source_compiler_invocations": 0, "object_loader_invocations": 0,
                         "compile_credit": False, "kernel_credit": False}
        qp = put(directory / "QUALIFICATION.json", raw(qualification))
        files[str(qp)] = self.identity(qp, "native-qualification-receipt")
        modules = {}
        for name in r.NATIVE_MODULES:
            info = native_rows[name]
            row = {"package": "goldbach", "source": info["source"], "object": resolutions[name],
                   "imports": info["direct_imports"], "git_blob_sha1": info["git_blob_sha1"],
                   "dependency_signatures": {d: modules[d]["closure_signature"] for d in info["direct_imports"] if ext.native(d)},
                   "provider": qualified[name]}
            bound = {k: row[k] for k in ("source", "object", "imports", "dependency_signatures", "provider")}
            bound.update(module=name, source_sha256=info["source_sha256"], object_sha256=files[row["object"]]["sha256"])
            row["closure_signature"] = ext.signature(bound)
            modules[name] = row
        value = {"schema": ext.SCHEMA, "status": ext.STATUS, "compile_credit": False, "kernel_credit": False,
                 "runtime": {"lean": str(self.lean), "leanchecker": str(self.checker), "sysroot": str(self.sysroot),
                             "mathlib_commit": self.mathlib_pin, "lean_path": [str(view), str(self.std_lib), str(self.core)]},
                 "packages": self.packages, "qualification": {"path": str(qp), "sha256": sha(qp.read_bytes()), "status": qualification["status"]},
                 "modules": modules, "files": files, "resolutions": resolutions,
                 "caller_scope": "P2.7 actual reachable native source closure; input qualification only"}
        value["context_signature"] = ext.signature(value)
        put(directory / "EXTERNAL_SNAPSHOT.json", raw(value))
        return value

    def binding(self, path, value):
        return {"schema": ext.SCHEMA, "snapshot": str(path), "snapshot_sha256": sha(path.read_bytes()),
                "context_signature": value["context_signature"], "verification_helper_sha256": sha(Path(ext.__file__).read_bytes()),
                "native_modules": sorted(value["modules"]),
                "lean_path": [str(self.lib), *value["runtime"]["lean_path"]], "lean_sysroot": str(self.sysroot)}

    def make_records(self, path, value):
        records, binding = {}, self.binding(path, value)
        nodes = project_nodes(self.root, r.ROOT)
        ext.mark_project_nodes(nodes, set(value["modules"]))
        for name, node in nodes.items():
            obj = put(self.lib / (name.replace(".", "/") + ".olean"), "project object " + name)
            rec = {"module": name, "source": str(node["source"].relative_to(self.root)),
                   "source_sha256": sha(node["source"].read_bytes()), "object": str(obj), "object_sha256": sha(obj.read_bytes()),
                   "deps": {d: records[d]["object_sha256"] for d in node["deps"]},
                   "dependency_signatures": {d: records[d]["closure_signature"] for d in node["deps"]},
                   "cache_schema": 3 if node["requires_external"] else 2, "toolchain": self.toolchain,
                   "exit_code": 0, "new_strict_compile": name in r.MODULES}
            if node["requires_external"]:
                rec.update(external_snapshot=binding, external_check={"status": "PASSED_BATCH_PRE_POST", "before": binding, "after": binding})
            if name in r.MODULES:
                command = [str(self.lean), *r.STRICT_FLAGS, "-o", str(obj), rec["source"]]
                log = ".lake/p2-private/logs/" + name + ".attempt1.log"
                put(self.root / log, b"")
                closure = set(project_nodes(self.root, name)) - {name}
                dep_files = {d: {k: records[d][k] for k in ("source_sha256", "object_sha256")} for d in closure}
                rec.update(command=command, attempts=[{"command": command, "exit_code": 0, "log": log}], log=log,
                           mathlib_commit=self.mathlib_pin, lean="4.33.0-rc1", dependency_file_check={
                               "modules": len(closure), "expected_sha256": json_digest(dep_files),
                               "before_sha256": json_digest(dep_files), "after_sha256": json_digest(dep_files),
                               "before_matches_records": True, "after_matches_records": True})
            rec["closure_signature"] = closure_signature(rec)
            records[name] = rec
        return records

    def adopt_currentchen(self):
        rec = copy.deepcopy(self.records[r.CURRENTCHEN])
        binding = self.binding(self.new_path, self.new)
        rec.update(new_strict_compile=False, kernel_credit=False, external_snapshot=binding,
                   external_check={"status": "PASSED_BATCH_PRE_POST", "before": binding, "after": binding})
        rec["closure_signature"] = closure_signature(rec)
        inputs = {str(self.sources[r.CURRENTCHEN]): self.identity(self.sources[r.CURRENTCHEN], "source"),
                  rec["object"]: self.identity(Path(rec["object"]), "object"),
                  str(self.new_path): self.identity(self.new_path, "qualified-native-snapshot")}
        for p in self.helper_paths:
            inputs[str(p)] = self.identity(p, "receiver-tool")
        receipt = {"schema": "p27-currentchen-historical-project-adoption-v1", "status": "EXACT_SOURCE_IMPORT_RUNTIME_REBIND_ONLY",
                   "module": r.CURRENTCHEN, "source_sha256": rec["source_sha256"], "object_sha256": rec["object_sha256"],
                   "closure_signature": rec["closure_signature"], "external_before": binding, "external_after": binding,
                   "source_compiler_invocations": 0, "object_loader_invocations": 0,
                   "new_strict_compile_credit": False, "kernel_credit": False, "physical_inputs": inputs}
        rp = put(self.root / ".lake/p27-currentchen-adoption/attempt-002/PROJECT_CACHE_ADOPTION.json", raw(receipt))
        rec["historical_cache_qualification"] = {"path": str(rp), "sha256": sha(rp.read_bytes())}
        current = copy.deepcopy(self.records)
        current[r.CURRENTCHEN] = rec
        put(self.registry, raw(current))

    def args(self):
        return SimpleNamespace(project_root=self.root, original_records=self.original_records_path,
                               original_records_sha256=self.original_records_sha, original_snapshot=self.old_path,
                               external_snapshot=self.new_path, out=self.out, capture_manifest_sha256=self.capture_sha)

    def make_capture(self):
        records = json.loads(self.original_records_path.read_bytes())
        inventory = {}
        for name in r.MODULES:
            rec = records[name]
            for relative in {rec["log"], *[attempt["log"] for attempt in rec["attempts"]]}:
                member = "COMPILE_LOG." + Path(relative).name
                data = (self.root / relative).read_bytes()
                inventory[relative] = {"module": name, "member": member, "sha256": sha(data), "bytes": len(data),
                                       "source_record_sha256": ext.signature(rec)}
                put(self.original_records_path.parent / member, data)
        metadata = {"schema": "p27-d734-original-registry-capture-v1", "status": "ORIGINAL_BYTES_CAPTURED_NOT_MIGRATED",
                    "original_job": r.ORIGINAL_JOB, "head": self.original_commit, "project": str(self.root),
                    "registry_sha256": self.original_records_sha, "registry_bytes": self.original_records_path.stat().st_size,
                    "snapshot_sha256": self.old_sha, "original_strict_modules": list(r.MODULES), "compile_logs": inventory,
                    "log_hash_boundary": "Hashes observed during capture; original compiler records did not contain log hashes.",
                    "capture_helper_sha256": sha(Path(r.__file__).read_bytes()), **r.CREDITS}
        cp = put(self.original_records_path.parent / "CAPTURE.json", raw(metadata))
        self.capture_sha = sha(cp.read_bytes())
        put(self.original_records_path.parent / "EXTERNAL_SNAPSHOT.json", self.old_path.read_bytes())

    def alter_original(self, change):
        value = json.loads(self.original_records_path.read_bytes())
        change(value)
        put(self.original_records_path, raw(value))
        self.original_records_sha = sha(self.original_records_path.read_bytes())
        self.make_capture()


class RebindTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fx = Fixture(Path(self.temp.name))
        self.patches = [patch.object(r, "ORIGINAL_PROJECT", str(self.fx.root)),
                        patch.object(r, "ORIGINAL_COMMIT", self.fx.original_commit),
                        patch.object(r, "ORIGINAL_SNAPSHOT_SHA", self.fx.old_sha),
                        patch.object(r, "LEAN", str(self.fx.lean)), patch.object(r, "MATHLIB", str(self.fx.mathlib)),
                        patch.object(r, "PIN", self.fx.mathlib_pin),
                        patch.dict(ext.PINS, {k: v["commit"] for k, v in self.fx.packages.items()}, clear=True)]
        for p in self.patches:
            p.start()
        self.before_objects = {str(p): sha(p.read_bytes()) for p in self.fx.lib.rglob("*.olean")}

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def assert_refused(self, pattern=None):
        registry = self.fx.registry.read_bytes()
        with self.assertRaises((ValueError, KeyError, OSError)) as cm:
            r.rebind(self.fx.args())
        if pattern:
            self.assertIn(pattern, str(cm.exception))
        self.assertEqual(registry, self.fx.registry.read_bytes())
        self.assertFalse(self.fx.out.exists())
        return cm.exception

    def test_exact_inputs_rebind_three_only_and_preserve_original_bytes(self):
        result = r.rebind(self.fx.args())
        self.assertEqual(result["status"], "TWO_NATIVE_RECORDS_REBOUND_ONE_NUMERIC_RETAINED")
        current = json.loads(self.fx.registry.read_bytes())
        before = json.loads(self.fx.current_before)
        self.assertEqual({n: v for n, v in current.items() if n not in r.MODULES},
                         {n: v for n, v in before.items() if n not in r.MODULES})
        self.assertEqual((self.fx.out / "ORIGINAL_RECORDS.json").read_bytes(), self.fx.original_records_path.read_bytes())
        self.assertEqual((self.fx.out / "ORIGINAL_EXTERNAL_SNAPSHOT.json").read_bytes(), self.fx.old_path.read_bytes())
        self.assertEqual(current[r.MODULES[0]], before[r.MODULES[0]])
        self.assertEqual(current[r.MODULES[0]]["cache_schema"], 2)
        for name in r.REBOUND_MODULES:
            row = current[name]
            self.assertFalse(row["new_strict_compile"])
            self.assertFalse(row["kernel_credit"])
            self.assertEqual(row["source_compiler_invocations"], 0)
            self.assertNotIn("command", row)
        self.assertEqual(self.before_objects, {str(p): sha(p.read_bytes()) for p in self.fx.lib.rglob("*.olean")})
        self.assertEqual(json.loads(self.fx.audit.read_bytes()), {"accepted": "untouched"})
        evidence = json.loads((self.fx.out / "RECORD_REBIND.json").read_bytes())
        self.assertEqual(set(evidence["changed_callers"]), {self.fx.changed_name})
        self.assertEqual(evidence["protected_project_count"], 13)
        self.assertEqual(evidence["status"], "EQUIVALENCE_VERIFIED_FOR_REGISTRY_CAS")
        self.assertEqual(evidence["retained"], list(r.RETAINED_MODULES))
        self.assertEqual(evidence["rebound"], list(r.REBOUND_MODULES))

    def test_bad_independent_registry_anchor(self):
        self.fx.original_records_sha = "0" * 64
        self.assert_refused("Original registry SHA")

    def test_bad_independent_capture_manifest_anchor(self):
        self.fx.capture_sha = "0" * 64
        self.assert_refused("Physical SHA differs")

    def test_tampered_captured_log_is_not_replaced_by_live_log(self):
        manifest = json.loads((self.fx.original_records_path.parent / "CAPTURE.json").read_bytes())
        first = next(iter(manifest["compile_logs"].values()))
        put(self.fx.original_records_path.parent / first["member"], b"tampered captured log")
        self.assert_refused("compile log inventory")

    def test_later_live_log_does_not_supply_original_authority(self):
        put(self.fx.root / self.fx.records[r.MODULES[1]]["log"], b"later unrelated live log")
        result = r.rebind(self.fx.args())
        self.assertEqual(result["rebound"], list(r.REBOUND_MODULES))
        captured = "COMPILE_LOG." + Path(self.fx.records[r.MODULES[1]]["log"]).name
        self.assertEqual((self.fx.out / captured).read_bytes(), b"")

    def test_capture_at_original_head_preserves_all_observed_raw_bytes(self):
        self.fx.sources[self.fx.changed_name].write_bytes(self.fx.original_sources[self.fx.changed_name])
        put(self.fx.registry, raw(self.fx.records))
        out = self.fx.root / ".lake/p27-native-record-rebind/fresh-capture"
        args = SimpleNamespace(project_root=self.fx.root, original_snapshot=self.fx.old_path, out=out)
        before = self.fx.registry.read_bytes()
        result = r.capture(args)
        self.assertEqual(result["registry_sha256"], sha(before))
        self.assertEqual(result["capture_manifest_sha256"], sha((out / "CAPTURE.json").read_bytes()))
        self.assertEqual((out / "records.json").read_bytes(), before)
        self.assertEqual(self.fx.registry.read_bytes(), before)
        self.assertEqual(len(result["compile_logs"]), 3)
        self.assertFalse(result["compile_credit"])
        self.assertEqual({str(p): sha(p.read_bytes()) for p in self.fx.lib.rglob("*.olean")}, self.before_objects)

    def test_capture_after_source_edit_refuses_even_when_head_unchanged(self):
        out = self.fx.root / ".lake/p27-native-record-rebind/refused-capture"
        args = SimpleNamespace(project_root=self.fx.root, original_snapshot=self.fx.old_path, out=out)
        before = self.fx.registry.read_bytes()
        with self.assertRaises(ValueError):
            r.capture(args)
        self.assertFalse(out.exists())
        self.assertEqual(self.fx.registry.read_bytes(), before)

    def test_capture_preserves_failed_attempt_log_as_history_too(self):
        self.fx.sources[self.fx.changed_name].write_bytes(self.fx.original_sources[self.fx.changed_name])
        records = copy.deepcopy(self.fx.records)
        name = r.MODULES[1]
        rec = records[name]
        first = rec["log"]
        last = first.replace(".attempt1.log", ".attempt2.log")
        put(self.fx.root / first, b"original failed attempt\n")
        put(self.fx.root / last, b"")
        rec["log"] = last
        rec["attempts"] = [{"command": rec["command"], "exit_code": 1, "log": first},
                           {"command": rec["command"], "exit_code": 0, "log": last}]
        put(self.fx.registry, raw(records))
        out = self.fx.root / ".lake/p27-native-record-rebind/multiple-attempt-capture"
        result = r.capture(SimpleNamespace(project_root=self.fx.root, original_snapshot=self.fx.old_path, out=out))
        self.assertEqual(len(result["compile_logs"]), 4)
        self.assertEqual((out / result["compile_logs"][first]["member"]).read_bytes(), b"original failed attempt\n")
        self.assertEqual(self.fx.registry.read_bytes(), raw(records))

    def test_original_git_bytes_are_checked_not_just_scope_self_hashes(self):
        changed_commit = commit(self.fx.root)
        with patch.object(r, "ORIGINAL_COMMIT", changed_commit):
            self.assert_refused("fixed Git blob")

    def test_failed_original_cannot_gain_success(self):
        self.fx.alter_original(lambda d: d[r.MODULES[0]].update(exit_code=1))
        self.assert_refused()

    def test_non_strict_original_not_a_supply(self):
        self.fx.alter_original(lambda d: d[r.MODULES[0]].update(new_strict_compile=False))
        self.assert_refused("original strict")

    def test_dependency_precheck_false(self):
        self.fx.alter_original(lambda d: d[r.MODULES[0]]["dependency_file_check"].update(before_matches_records=False))
        self.assert_refused("dependency file")

    def test_forged_dependency_digest(self):
        self.fx.alter_original(lambda d: d[r.MODULES[0]]["dependency_file_check"].update(before_sha256="0" * 64))
        self.assert_refused("dependency file")

    def test_original_post_batch_binding_wrong(self):
        self.fx.alter_original(lambda d: d[r.REBOUND_MODULES[0]]["external_check"].update(after={}))
        self.assert_refused()

    def test_original_command_not_trust_zero(self):
        self.fx.alter_original(lambda d: d[r.MODULES[0]]["command"].__setitem__(1, "-t1"))
        self.assert_refused("original strict")

    def test_arbitrary_style_exceptions_are_not_authorized(self):
        self.fx.alter_original(lambda d: d[r.MODULES[0]]["command"].insert(7, "-Dlinter.unusedVariables=false"))
        self.assert_refused("fallback flags require original-log review")

    def test_changed_protected_source(self):
        self.fx.sources[self.fx.numbers[-1]].write_text("def changed := 2\n")
        self.assert_refused()

    def test_changed_project_object(self):
        put(Path(self.fx.records[r.MODULES[0]]["object"]), b"changed")
        self.assert_refused()

    def test_extra_project_loadable_facet(self):
        obj = Path(self.fx.records[r.MODULES[1]]["object"])
        put(Path(str(obj) + ".private"), b"extra")
        self.assert_refused("Extra unrecorded project facet")

    def test_extra_native_loadable_facet(self):
        obj = Path(self.fx.new["resolutions"][r.NATIVE_MODULES[0]])
        put(Path(str(obj)[:-6] + ".ir"), b"extra")
        self.assert_refused("Unbound loadable facet")

    def test_changed_runtime_payload(self):
        put(self.fx.runtime_files[-1], b"different ABI")
        self.assert_refused()

    def test_changed_old_native_object_even_if_new_is_same(self):
        put(Path(self.fx.old["resolutions"][r.NATIVE_MODULES[0]]), b"changed old object")
        self.assert_refused()

    def test_changed_import_ir_bytes(self):
        put(self.fx.std_ir, b"changed imported IR")
        self.assert_refused()

    def test_currentchen_old_adoption_is_not_fresh(self):
        current = json.loads(self.fx.registry.read_bytes())
        current[r.CURRENTCHEN] = self.fx.records[r.CURRENTCHEN]
        put(self.fx.registry, raw(current))
        self.assert_refused()

    def test_extra_new_snapshot_module(self):
        value = copy.deepcopy(self.fx.new)
        value["modules"]["MathlibNt.Unknown"] = value["modules"][r.NATIVE_MODULES[0]]
        value.pop("context_signature")
        value["context_signature"] = ext.signature(value)
        put(self.fx.new_path, raw(value))
        self.assert_refused()

    def test_existing_output_is_not_overwritten(self):
        self.fx.out.mkdir(parents=True)
        put(self.fx.out / "owned-by-another-task", b"retain")
        with self.assertRaises(ValueError):
            r.rebind(self.fx.args())
        self.assertEqual((self.fx.out / "owned-by-another-task").read_bytes(), b"retain")
        self.assertEqual(self.fx.registry.read_bytes(), self.fx.current_before)

    def test_cas_refuses_concurrent_writer_without_partial_update(self):
        writer_bytes = self.fx.current_before + b"\n"
        original = r.publish_transaction
        def racing(*args, **kwargs):
            put(self.fx.registry, writer_bytes)
            return original(*args, **kwargs)
        with patch.object(r, "publish_transaction", racing):
            with self.assertRaisesRegex(ValueError, "registry"):
                r.rebind(self.fx.args())
        self.assertEqual(self.fx.registry.read_bytes(), writer_bytes)
        self.assertFalse(self.fx.out.exists())

    def test_precommit_write_failure_leaves_no_partial_registry(self):
        original = r.write_exclusive
        def failing(path, data):
            if path.name == "RECORD_REBIND.json":
                raise OSError("fixture storage failure")
            return original(path, data)
        with patch.object(r, "write_exclusive", failing):
            self.assert_refused("storage failure")

    def test_late_facet_after_evidence_staging_aborts_registry_commit(self):
        original = r.write_exclusive
        def inject(path, data):
            original(path, data)
            if path.name == "RECORD_REBIND.json":
                obj = Path(self.fx.records[r.MODULES[1]]["object"])
                put(Path(str(obj) + ".private"), b"late unexpected facet")
        with patch.object(r, "write_exclusive", inject):
            self.assert_refused("Extra unrecorded project facet")

    def test_duplicate_original_json_key_refused_even_with_matching_outer_sha(self):
        original = self.fx.original_records_path.read_bytes()
        duplicate = b'{"duplicate":0,"duplicate":1,' + original[1:]
        put(self.fx.original_records_path, duplicate)
        self.fx.original_records_sha = sha(duplicate)
        self.assert_refused("Duplicate JSON key")


if __name__ == "__main__":
    unittest.main()
