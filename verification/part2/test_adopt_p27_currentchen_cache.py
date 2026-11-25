"""Compiler-free acceptance-boundary tests for the one CurrentChen receiver."""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

try:
    import adopt_p27_currentchen_cache as a
except ModuleNotFoundError:
    a = None


class CurrentChenReceiverTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(a, "Single-module historical receiver is not implemented")
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def event(self):
        arguments = ["-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000", *a.ORIGINAL_INPUT_ARGS]
        return {"tool": "lean", "cwd": a.P6_ROOT, "sysroot": a.P6_SHADOW,
                "command": [a.P6_SHADOW + "/bin/lean-runtime", "-t0", "-j2", "-M12288",
                            "-D", "maxRecDepth=100000", "-D", "maxHeartbeats=4000000", *a.ORIGINAL_INPUT_ARGS],
                "input_args": arguments}

    def test_original_d_option_spelling_is_normalized_without_losing_options(self):
        normalized = a.validate_source_event(self.event())
        self.assertEqual(normalized["options"], {"maxRecDepth": "100000", "maxHeartbeats": "4000000"})
        self.assertEqual(normalized["arguments"], a.ORIGINAL_INPUT_ARGS)

    def test_guarded_source_event_cannot_use_nonzero_trust(self):
        event = self.event()
        event["command"][1] = "-t1"
        with self.assertRaisesRegex(ValueError, "trust-zero"):
            a.validate_source_event(event)

    def test_unrecorded_option_and_duplicate_option_are_rejected(self):
        for extra in ("-DwarningAsError=false", "-DmaxHeartbeats=4000000"):
            with self.subTest(extra=extra):
                event = self.event()
                event["input_args"].insert(0, extra)
                with self.assertRaises(ValueError):
                    a.validate_source_event(event)

    def test_source_event_from_member_is_not_a_p6_provider(self):
        event = self.event()
        event["cwd"] = "/workspace/blue-member-build"
        with self.assertRaisesRegex(ValueError, "P6 source event"):
            a.validate_source_event(event)

    def test_source_event_for_another_output_is_rejected(self):
        event = self.event()
        event["input_args"][event["input_args"].index("-o") + 1] = "/tmp/another.olean"
        with self.assertRaisesRegex(ValueError, "source/output"):
            a.validate_source_event(event)

    def test_exact_published_source_and_output_index_is_usable(self):
        repo = Path(a.__file__).resolve().parents[2]
        raw = subprocess.check_output(["git", "show", "HEAD:" + a.INDEX_REPO_PATH], cwd=repo)
        row = a.validate_index_pair(raw, raw)
        self.assertEqual(row["source"]["sha256"], a.SOURCE_SHA)
        self.assertEqual(row["facets"]["olean"]["sha256"], a.OBJECT_SHA)

    def test_mutated_historical_index_is_not_repaired_from_current_files(self):
        with self.assertRaisesRegex(ValueError, "original project index"):
            a.validate_index_pair(b"{}", b"{}")

    def test_different_existing_object_is_never_overwritten(self):
        lib = self.root / "lib"
        candidate = self.root / "candidate"
        candidate.write_bytes(b"original cache")
        target = lib / (a.MODULE.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True)
        target.write_bytes(b"another object")
        with self.assertRaisesRegex(ValueError, "different project object"):
            a.install_project_object(lib, candidate, hashlib.sha256(candidate.read_bytes()).hexdigest())
        self.assertEqual(target.read_bytes(), b"another object")

    def test_extra_project_facet_is_not_silently_retained(self):
        lib = self.root / "lib"
        candidate = self.root / "candidate"
        candidate.write_bytes(b"original cache")
        extra = lib / (a.MODULE.replace(".", "/") + ".ir")
        extra.parent.mkdir(parents=True)
        extra.write_bytes(b"unbound old IR")
        with self.assertRaisesRegex(ValueError, "Extra unqualified"):
            a.install_project_object(lib, candidate, hashlib.sha256(candidate.read_bytes()).hexdigest())
        self.assertFalse(extra.with_suffix(".olean").exists())

    def test_installed_object_is_an_independent_copy(self):
        candidate = self.root / "candidate"
        candidate.write_bytes(b"original cache")
        target = a.install_project_object(self.root / "lib", candidate, hashlib.sha256(candidate.read_bytes()).hexdigest())
        self.assertFalse(target.is_symlink())
        target.write_bytes(b"future local object")
        self.assertEqual(candidate.read_bytes(), b"original cache")

    def test_extra_facet_is_rejected_before_existing_record_fast_path(self):
        receiver = a.CurrentChenReceiver.__new__(a.CurrentChenReceiver)
        receiver.private_lib = self.root / "lib"
        extra = receiver.private_lib / (a.MODULE.replace(".", "/") + ".ir")
        extra.parent.mkdir(parents=True)
        extra.write_bytes(b"unbound")
        with self.assertRaisesRegex(ValueError, "Extra unqualified"):
            receiver.run()

    def record_fixture(self):
        source = self.root / (a.MODULE.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True)
        source.write_text("import " + a.TAIL + "\n")
        obj = self.root / "lib" / (a.MODULE.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True)
        obj.write_bytes(b"qualified historical object")
        toolchain = {"lean_version": "fixture", "lean_binary_sha256": "a" * 64, "mathlib_commit": a.MATHLIB_PIN}
        external = {"native_modules": [a.TAIL], "context_signature": "b" * 64}
        record = a.make_record(self.root, source, obj, toolchain, external)
        nodes = {a.MODULE: {"source": source, "deps": []}}
        frozen = {"project": {a.MODULE: {"source": record["source"], "source_sha256": record["source_sha256"],
                                        "object": str(obj), "object_sha256": record["object_sha256"]}},
                  "toolchain": toolchain, "lean_binary_sha256": "a" * 64, "external_snapshot": external}
        return record, nodes, frozen

    def test_historical_record_matches_existing_schema3_verifier_without_new_compile_credit(self):
        record, nodes, frozen = self.record_fixture()
        self.assertEqual(record["cache_schema"], 3)
        self.assertFalse(record["new_strict_compile"])
        self.assertFalse(record["kernel_credit"])
        self.assertEqual(record["deps"], {})
        self.assertEqual(record["dependency_signatures"], {})
        a.verify_compilation({a.MODULE: record}, nodes, frozen)

    def test_schema3_record_does_not_survive_environment_drift(self):
        record, nodes, frozen = self.record_fixture()
        frozen = copy.deepcopy(frozen)
        frozen["external_snapshot"]["context_signature"] = "c" * 64
        with self.assertRaisesRegex(ValueError, "context"):
            a.verify_compilation({a.MODULE: record}, nodes, frozen)

    def test_registry_concurrent_writer_is_not_overwritten(self):
        registry = self.root / "records.json"
        old = b"{}\n"
        registry.write_bytes(old)
        changed = b'{"another_writer":true}\n'
        registry.write_bytes(changed)
        with self.assertRaisesRegex(ValueError, "Another writer"):
            a.commit_record(registry, old, {a.MODULE: {"new_strict_compile": False}})
        self.assertEqual(registry.read_bytes(), changed)

    def test_registry_commit_retains_unrelated_records(self):
        registry = self.root / "records.json"
        old = b'{"ImbalancedChen.Other":{"immutable":"previous"}}\n'
        registry.write_bytes(old)
        records = json.loads(old)
        records[a.MODULE] = {"new_strict_compile": False}
        a.commit_record(registry, old, records)
        self.assertEqual(json.loads(registry.read_text())["ImbalancedChen.Other"], {"immutable": "previous"})


if __name__ == "__main__":
    unittest.main()
