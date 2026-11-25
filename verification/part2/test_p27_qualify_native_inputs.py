"""Compiler-free refusal tests for the independent P2.7 input adapter."""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

try:
    import p27_qualify_native_inputs as q
except ModuleNotFoundError:
    q = None


class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(q, "The P2.7 input adapter is not implemented")
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def transfer(self, data=b"original bytes", original="/old/Module.olean"):
        sha = hashlib.sha256(data).hexdigest()
        payload = self.root / "objects" / sha
        payload.parent.mkdir(exist_ok=True)
        payload.write_bytes(data)
        manifest = {"schema": "p27-native-byte-transfer-v1", "compile_credit": False,
                    "kernel_credit": False, "files": {original: {
                        "relative_path": "objects/" + sha, "sha256": sha, "bytes": len(data)}}}
        (self.root / "MANIFEST.json").write_text(json.dumps(manifest))
        return manifest, payload, sha

    def test_transport_manifest_does_not_replace_an_original_expected_hash(self):
        _, _, sha = self.transfer()
        transfer = q.NativeTransfer(self.root, q.PhysicalHashes())
        self.assertTrue(transfer.get("/old/Module.olean", sha).is_file())
        with self.assertRaisesRegex(ValueError, "original SHA"):
            transfer.get("/old/Module.olean", "f" * 64)

    def test_transport_rejects_traversal(self):
        manifest, _, _ = self.transfer()
        manifest["files"]["/old/Module.olean"]["relative_path"] = "../elsewhere"
        (self.root / "MANIFEST.json").write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "transport path"):
            q.NativeTransfer(self.root, q.PhysicalHashes())

    def test_transport_rejects_symlink_payload(self):
        _, payload, _ = self.transfer()
        saved = self.root / "elsewhere"
        payload.rename(saved)
        payload.symlink_to(saved)
        with self.assertRaisesRegex(ValueError, "symlink"):
            q.NativeTransfer(self.root, q.PhysicalHashes())

    def test_transport_rechecks_mutated_bytes(self):
        _, payload, sha = self.transfer()
        transfer = q.NativeTransfer(self.root, q.PhysicalHashes())
        payload.write_bytes(b"changed bytes!")
        with self.assertRaisesRegex(ValueError, "transport bytes"):
            transfer.get("/old/Module.olean", sha)

    def test_original_import_order_is_preserved_and_hash_checked(self):
        paths = ["/old/lib/Mathlib/Fixture.olean", "/old/lib/Mathlib/Fixture.ir"]
        receipts = {p: {"sha256": str(i + 1) * 64} for i, p in enumerate(paths)}
        setup = {"importArts": {"Mathlib.Fixture": [[paths[0]], [paths[1]]]}}
        expected = {"Mathlib.Fixture": [[p, receipts[p]["sha256"]] for p in paths]}
        self.assertEqual(q.ordered_import_map(setup, "/old", receipts, q.signature(expected)), expected)
        setup["importArts"]["Mathlib.Fixture"].reverse()
        with self.assertRaisesRegex(ValueError, "map SHA"):
            q.ordered_import_map(setup, "/old", receipts, q.signature(expected))

    def test_original_import_requires_each_real_receipt(self):
        setup = {"importArts": {"Mathlib.Fixture": [["lib/Mathlib/Fixture.olean"]]}}
        with self.assertRaisesRegex(ValueError, "lacks SHA"):
            q.ordered_import_map(setup, "/old", {})

    def test_original_import_duplicate_groups_rejected(self):
        group = ["Mathlib.Fixture", [["/old/Fixture.olean"]]]
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            q.ordered_import_map({"importArts": [group, group]}, "/old",
                                 {"/old/Fixture.olean": {"sha256": "a" * 64}})

    def test_project_scope_follows_actual_imports_and_rejects_cycles(self):
        sources = {q.ROOT: "import ImbalancedChen.Child\nimport MathlibNt.Required\n",
                   "ImbalancedChen.Child": "import Mathlib.Data.Real.Basic\n",
                   "ImbalancedChen.Unrelated": "import MathlibNt.Unrelated\n"}
        for name, text in sources.items():
            path = self.root / (name.replace(".", "/") + ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        nodes, order = q.project_census(self.root, q.PhysicalHashes())
        self.assertEqual(set(nodes), {q.ROOT, "ImbalancedChen.Child"})
        self.assertEqual(order[-1], q.ROOT)
        (self.root / "ImbalancedChen/Child.lean").write_text("import " + q.ROOT + "\n")
        with self.assertRaisesRegex(ValueError, "cycle"):
            q.project_census(self.root, q.PhysicalHashes())

    def test_p6_recheck_list_rejects_duplicate_and_failed_original_checks(self):
        row = {"module": "Mathlib.Fixture", "P6_path": "/p6/Fixture.olean",
               "Member_path": "/member/Fixture.olean", "sha256": "a" * 64,
               "same_actual_object_bytes_reconfirmed": True, "method": "original method"}
        self.assertEqual(len(q.p6_recheck_table([row], 1, q.signature([row]))), 1)
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            q.p6_recheck_table([row, row], 2, q.signature([row, row]))
        failed = dict(row, same_actual_object_bytes_reconfirmed=False)
        with self.assertRaisesRegex(ValueError, "not reconfirmed"):
            q.p6_recheck_table([failed], 1, q.signature([failed]))

    def test_p6_rechecks_cannot_be_replaced_by_a_compact_summary(self):
        with self.assertRaisesRegex(ValueError, "count"):
            q.p6_recheck_table([], 16622, "a" * 64)

    def test_p6_setup_must_cover_each_anchored_recheck_exactly_once(self):
        self.assertTrue(callable(getattr(q, "p6_setup_map", None)), "P6 exact setup coverage gate is missing")
        rows = {"/p6/Fixture.olean": {"module": "Mathlib.Fixture", "sha256": "a" * 64},
                "/p6/Other.olean": {"module": "Mathlib.Other", "sha256": "b" * 64}}
        setup = {"importArts": {"Mathlib.Fixture": [["/p6/Fixture.olean"]]}}
        with self.assertRaisesRegex(ValueError, "complete original import"):
            q.p6_setup_map(setup, "/p6", rows)

    def test_compact_p6_bytes_cannot_masquerade_as_complete_original_receipt(self):
        self.transfer(b'{"compact_extraction_only":true}', q.P6_RECEIPT)
        obj = q.P27Qualification.__new__(q.P27Qualification)
        q.InputBindings.__init__(obj, q.PhysicalHashes())
        obj.bundle = q.NativeTransfer(self.root, obj.hashes)
        with self.assertRaisesRegex(ValueError, "original SHA"):
            obj.p6_provider(q.TAIL)

    def test_missing_independent_checkpoint_provider_stays_blocked(self):
        obj = q.P27Qualification.__new__(q.P27Qualification)
        obj.selected, obj.omitted = {}, {"MathlibNt.Fixture": "NO_SOURCE_MATCHING_ORIGINAL_GUARDED_ROW"}
        with self.assertRaisesRegex(ValueError, "NO_SOURCE_MATCHING_ORIGINAL_GUARDED_ROW"):
            obj.checkpoint_provider("MathlibNt.Fixture")

    def test_checkpoint_quarantine_is_not_upgraded(self):
        obj = q.P27Qualification.__new__(q.P27Qualification)
        obj.selected = {"Architect.Command": {"original_classification": q.carrier.ARCHITECT_QUARANTINE}}
        obj.omitted = {}
        with self.assertRaisesRegex(ValueError, "ORIGINAL_QUARANTINE_RETAINED"):
            obj.checkpoint_provider("Architect.Command")

    def prerequisite_event(self, leaf="LiLiuPrereqBuchstabFunction", pid=20291):
        package = "/workspace/blue-p6-build/.lake/packages/goldbach"
        module = "MathlibNt/SieveTheory/" + leaf
        args = [package + "/" + module + ".lean",
                "-o", package + "/.lake/build/lib/lean/" + module + ".olean",
                "-i", package + "/.lake/build/lib/lean/" + module + ".ilean",
                "-c", package + "/.lake/build/ir/" + module + ".c",
                "--setup", package + "/.lake/build/ir/" + module + ".setup.json", "--json"]
        shadow = "/workspace/blue-build-tools/runtime/p0-ci-shadow-toolchain"
        return {"pid": pid, "tool": "lean", "cwd": "/workspace/blue-p6-build",
                "sysroot": shadow, "slot_owner": str(pid), "input_args": args,
                "command": [shadow + "/bin/lean-runtime", "-t0", "-j2", "-M12288"] + args}

    def test_prerequisite_events_bind_each_own_source_output_and_guard(self):
        self.assertTrue(callable(getattr(q, "p6_prerequisite_event", None)),
                        "Two explicit P6 prerequisite source gates are missing")
        for leaf, pid in [("LiLiuPrereqBuchstabFunction", 20291), ("LiLiuPrereqBuchstabBounds", 20310)]:
            name = "MathlibNt.SieveTheory." + leaf
            event = self.prerequisite_event(leaf, pid)
            self.assertEqual(q.p6_prerequisite_event(name, event), event)
            mutations = []
            bad = copy.deepcopy(event); bad["command"][1] = "-t1"; mutations.append(bad)
            bad = copy.deepcopy(event); bad["slot_owner"] = "another-slot"; mutations.append(bad)
            bad = copy.deepcopy(event); bad["pid"] += 1; mutations.append(bad)
            bad = copy.deepcopy(event); bad["input_args"][2] += ".other"; mutations.append(bad)
            bad = copy.deepcopy(event); bad["command"].append("-Ddebug.skipKernelTC=true"); mutations.append(bad)
            bad = copy.deepcopy(event); bad["cwd"] = "/workspace/blue-member-build"; mutations.append(bad)
            for bad in mutations:
                with self.subTest(leaf=leaf, bad=bad), self.assertRaises(ValueError):
                    q.p6_prerequisite_event(name, bad)
        with self.assertRaisesRegex(ValueError, "scoped"):
            q.p6_prerequisite_event(q.TAIL, self.prerequisite_event())

    def prerequisite_map_fixture(self):
        original = {"Mathlib.Fixture": [["/p6/Fixture.olean", "a" * 64]]}
        expected = hashlib.sha256(json.dumps(original, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        rows = {"/p6/Fixture.olean": {"module": "Mathlib.Fixture", "sha256": "a" * 64},
                "/p6/Unused.olean": {"module": "Mathlib.Unused", "sha256": "b" * 64}}
        setup = {"importArts": {"Mathlib.Fixture": [["/p6/Fixture.olean"]]}}
        return setup, rows, original, expected

    def test_prerequisite_subset_uses_only_its_own_exact_imports(self):
        self.assertTrue(callable(getattr(q, "p6_subset_map", None)), "Exact P6 subset gate is missing")
        setup, rows, original, expected = self.prerequisite_map_fixture()
        self.assertEqual(q.p6_subset_map(setup, "/p6", rows, expected, 1, 1, []), original)
        for change in ("wrong-module", "duplicate-facet", "extra-native", "wrong-map-hash"):
            s, r = copy.deepcopy(setup), copy.deepcopy(rows)
            sha = expected
            if change == "wrong-module": r["/p6/Fixture.olean"]["module"] = "Mathlib.Other"
            if change == "duplicate-facet": s["importArts"]["Mathlib.Fixture"][0] *= 2
            if change == "extra-native":
                s["importArts"]["MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation"] = [["/p6/Tail.olean"]]
                r["/p6/Tail.olean"] = {"module": "MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation", "sha256": "c" * 64}
            if change == "wrong-map-hash": sha = "f" * 64
            with self.subTest(change=change), self.assertRaises(ValueError):
                q.p6_subset_map(s, "/p6", r, sha, 1, 1, [])

    def test_completed_prerequisite_outputs_are_required_without_inventing_exit_code(self):
        self.assertTrue(callable(getattr(q, "p6_completed_outputs", None)), "Completed-output gate is missing")
        outputs = {}
        for suffix in (".olean", ".ilean", ".c"):
            path = self.root / ("Fixture" + suffix)
            path.write_bytes(b"bound output")
            outputs[suffix] = path
        trace = {"schemaVersion": "2025-09-10", "synthetic": False, "depHash": "1234",
                 "outputs": {"o": ["o.olean"], "i": "i.ilean", "c": "c.c"}}
        self.assertTrue(q.p6_completed_outputs(trace, outputs))
        for missing in ("o", "i", "c"):
            bad = copy.deepcopy(trace); del bad["outputs"][missing]
            with self.subTest(missing=missing), self.assertRaisesRegex(ValueError, "completed"):
                q.p6_completed_outputs(bad, outputs)
        outputs[".c"].write_bytes(b"")
        with self.assertRaisesRegex(ValueError, "completed"):
            q.p6_completed_outputs(trace, outputs)

    def test_prerequisite_path_does_not_replace_checkpoint_quarantine(self):
        self.assertTrue(callable(getattr(q.P27Qualification, "missing_provider", None)),
                        "Narrow missing-provider dispatch is missing")
        name = "MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction"
        obj = q.P27Qualification.__new__(q.P27Qualification)
        obj.selected = {name: {"original_classification": q.carrier.ARCHITECT_QUARANTINE}}
        obj.omitted = {}
        with self.assertRaisesRegex(ValueError, "ORIGINAL_QUARANTINE_RETAINED"):
            obj.missing_provider(name)
        obj.selected, obj.omitted = {}, {name: "A_DIFFERENT_ORIGINAL_REFUSAL"}
        with self.assertRaisesRegex(ValueError, "original refusal"):
            obj.missing_provider(name)

    def test_bounds_import_cannot_use_an_unqualified_function_object(self):
        obj = q.P27Qualification.__new__(q.P27Qualification)
        name = "MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction"
        obj.nodes, obj.qualified = {name: {}}, {}
        with self.assertRaisesRegex(ValueError, "own qualified provider"):
            obj.import_artifact(name, "/p6/LiLiuPrereqBuchstabFunction.olean", "a" * 64)

    def runtime_binding_fixture(self):
        sysroot = self.root / "current-runtime"
        (sysroot / "bin").mkdir(parents=True)
        physical, hashes = {}, {}
        for name in ("lean", "leanir", "clang", "leanc", "llvm-ar", "lake", "leanchecker", "leantar"):
            path = sysroot / "bin" / name
            path.write_bytes(("original-" + name).encode())
            hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
            physical[str(path)] = {"sha256": hashes[name]}
        old = {"/original/bin/" + n: sha for n, sha in hashes.items()}
        old.update({q.P6_SHADOW + "/bin/" + n: hashes["lean" if n == "lean-runtime" else n]
                    for n in ("lean-runtime", "lake", "leantar")})
        tools = ["lean", "leanir", "clang", "leanc", "llvm-ar"]
        old.update({q.P6_SHADOW + "/bin/" + n: "f" * 64 for n in tools})
        obj = q.P27Qualification.__new__(q.P27Qualification)
        q.InputBindings.__init__(obj, q.PhysicalHashes())
        obj.base = SimpleNamespace(value={"runtime": {"sysroot": str(sysroot)}}, files=physical)
        return obj, {"shadow": q.P6_SHADOW, "tools": tools, "runtime_sha256": old}, sysroot

    def test_prerequisite_runtime_rebinds_all_eleven_original_payloads(self):
        self.assertTrue(callable(getattr(q.P27Qualification, "p6_runtime_bindings", None)),
                        "Independent P6 prerequisite ABI rebinding is missing")
        obj, state, sysroot = self.runtime_binding_fixture()
        bound = obj.p6_runtime_bindings(state)
        self.assertEqual(len(bound), 11)
        self.assertEqual(len(obj.bound), 8)
        self.assertTrue(all(row["current"].startswith(str(sysroot)) for row in bound))
        (sysroot / "bin/clang").write_bytes(b"different-compiler-payload")
        with self.assertRaisesRegex(ValueError, "SHA"):
            obj.p6_runtime_bindings(state)

    def test_prerequisite_runtime_requires_each_payload_in_qualified_base(self):
        self.assertTrue(callable(getattr(q.P27Qualification, "p6_runtime_bindings", None)),
                        "Independent P6 prerequisite ABI rebinding is missing")
        obj, state, sysroot = self.runtime_binding_fixture()
        del obj.base.files[str(sysroot / "bin/leanchecker")]
        with self.assertRaisesRegex(ValueError, "qualified current runtime"):
            obj.p6_runtime_bindings(state)

    def metadata_fixture(self, *, descriptor="authentic.output"):
        name = "MathlibNt.Fixture"
        old = "/original/.lake/packages/goldbach"
        stem = old + "/.lake/build/lib/lean/MathlibNt/Fixture"
        files = {stem + ".olean": b"portable fixture",
                 stem + ".olean.hash": b"authentic\n",
                 stem + ".trace": json.dumps({"schemaVersion": "2025-09-10", "synthetic": False,
                                              "outputs": {"o": [descriptor]}}).encode(),
                 old + "/.lake/build/ir/MathlibNt/Fixture.setup.json": json.dumps({
                     "name": name, "package": "goldbach", "options": {}, "plugins": [], "dynlibs": [],
                     "importArts": {}}).encode()}
        bundle = self.root / "bundle"
        (bundle / "objects").mkdir(parents=True)
        manifest = {"schema": "p27-native-byte-transfer-v1", "compile_credit": False,
                    "kernel_credit": False, "files": {}}
        facets = []
        for original, raw in files.items():
            sha = hashlib.sha256(raw).hexdigest()
            (bundle / "objects" / sha).write_bytes(raw)
            manifest["files"][original] = {"relative_path": "objects/" + sha, "sha256": sha, "bytes": len(raw)}
            facets.append({"original_path": original, "sha256": sha, "bytes": len(raw)})
        (bundle / "MANIFEST.json").write_text(json.dumps(manifest))
        obj = q.P27Qualification.__new__(q.P27Qualification)
        q.InputBindings.__init__(obj, q.PhysicalHashes())
        obj.bundle = q.NativeTransfer(bundle, obj.hashes)
        obj.out = self.root / "out"
        obj.out.mkdir()
        obj.nodes = {name: {"package": "goldbach"}}
        project = Path(q.__file__).resolve().parents[2]
        original = subprocess.check_output(["git", "show", "HEAD:" + str(q.PROTOCOL.relative_to(project))], cwd=project)
        self.assertEqual(hashlib.sha256(original).hexdigest(), q.PROTOCOL_SHA256)
        helper = self.root / "original_protocol.py"
        helper.write_bytes(original)
        spec = importlib.util.spec_from_file_location("test_p27_original_protocol", helper)
        obj.protocol = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(obj.protocol)
        return obj, name, facets, old

    def test_real_portable_metadata_uses_unchanged_descriptor_validator(self):
        obj, name, facets, old = self.metadata_fixture()
        setup, objects, metadata = obj.metadata(name, facets, old)
        self.assertEqual(setup["name"], name)
        self.assertEqual(set(objects), {".olean"})
        self.assertTrue(all(r["matched"] for r in metadata["descriptor_checks"]))
        self.assertIn(metadata["setup"], obj.bound)
        self.assertIn(metadata["trace"], obj.bound)

    def test_false_original_descriptor_stays_rejected(self):
        obj, name, facets, old = self.metadata_fixture(descriptor="different.output")
        with self.assertRaisesRegex(ValueError, "descriptors"):
            obj.metadata(name, facets, old)

    def test_changed_previously_bound_file_rejected(self):
        binder = q.InputBindings(q.PhysicalHashes())
        path = self.root / "input"
        path.write_bytes(b"before")
        binder.bind(path, "fixture")
        path.write_bytes(b"after!")
        with self.assertRaisesRegex(ValueError, "Previously bound"):
            binder.bind(path, "fixture")

    def test_view_does_not_overwrite_an_existing_namespace_file(self):
        payload = self.root / "source.olean"
        payload.write_bytes(b"old provider")
        view = self.root / "view"
        q.install_view_module(view, "MathlibNt.Fixture", {".olean": payload}, copy=False)
        with self.assertRaisesRegex(ValueError, "overwrite"):
            q.install_view_module(view, "MathlibNt.Fixture", {".olean": payload}, copy=False)
        self.assertEqual(payload.read_bytes(), b"old provider")

    def test_view_rejects_executable_facets(self):
        payload = self.root / "input"
        payload.write_bytes(b"data")
        with self.assertRaisesRegex(ValueError, "loadable"):
            q.install_view_module(self.root / "view", "MathlibNt.Fixture",
                                  {".olean": payload, ".so": payload}, copy=False)

    def test_existing_consumer_requires_complete_new_native_namespace(self):
        old = self.root / "old/MathlibNt/Existing.olean"
        old.parent.mkdir(parents=True)
        old.write_bytes(b"old qualified object")
        new = self.root / "new.olean"
        new.write_bytes(b"new qualified object")
        view = self.root / "view"
        q.install_view_module(view, "MathlibNt.Additional", {".olean": new}, copy=True)
        additional = view / "MathlibNt/Additional.olean"
        consumer = q.ExternalSnapshot.__new__(q.ExternalSnapshot)
        consumer.search_path = [view, self.root / "old"]
        consumer.value = {"resolutions": {"MathlibNt.Existing": str(old), "MathlibNt.Additional": str(additional)}}
        consumer.files = {str(old): {}, str(additional): {}}
        with self.assertRaisesRegex(ValueError, "shadows"):
            consumer.verify_resolutions()
        q.install_view_module(view, "MathlibNt.Existing", {".olean": old}, copy=False)
        consumer.verify_resolutions()

    def test_consumer_rejection_never_publishes_a_complete_snapshot(self):
        out = self.root / "out"
        out.mkdir()
        with self.assertRaisesRegex(ValueError, "qualification"):
            q.publish_snapshot({}, out, "/no/lean", "pin", self.root / "project-lib")
        self.assertFalse((out / "EXTERNAL_SNAPSHOT.json").exists())

    def test_failure_after_publish_removes_consumable_name(self):
        out = self.root / "out"
        out.mkdir()
        with patch.object(q, "ExternalSnapshot", side_effect=[unittest.mock.Mock(), ValueError("changed after publication")]):
            with self.assertRaisesRegex(ValueError, "changed after"):
                q.publish_snapshot({}, out, "/no/lean", "pin", self.root / "project-lib")
        self.assertFalse((out / "EXTERNAL_SNAPSHOT.json").exists())
        self.assertTrue((out / "REJECTED_EXTERNAL_SNAPSHOT.json").exists())


if __name__ == "__main__":
    unittest.main()
