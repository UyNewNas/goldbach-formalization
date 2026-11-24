"""Exercise native-context provenance with fixture executables, never Lean credit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

import test_private_cache_binding as cache_tests
import test_private_audit as audit_tests
import winner9_external_snapshot as native_env


class NativeFixture:
    def __init__(self, fixture, checker: Path | None = None) -> None:
        self.fixture = fixture
        self.root = fixture.base / "native-source"
        self.source = self.root / "MathlibNt/Fixture.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("def fixtureNativeValue : Nat := 0\n")
        for args in (["init", "-q"], ["add", "MathlibNt/Fixture.lean"],
                     ["-c", "user.name=Cache Test", "-c", "user.email=cache@example.invalid",
                      "commit", "-qm", "native fixture"]):
            subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)
        self.pin = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.root, text=True).strip()
        self.patch = patch.dict(native_env.PINS, {"goldbach": self.pin, "LeanArchitect": self.pin}, clear=True)
        self.patch.start()
        fixture.addCleanup(self.patch.stop)
        self.lib = fixture.base / "native-lib"
        self.obj = self.lib / "MathlibNt/Fixture.olean"
        self.obj.parent.mkdir(parents=True)
        self.obj.write_bytes(b"native fixture object")
        self.sysroot = fixture.base / "runtime"
        (self.sysroot / "lib/lean").mkdir(parents=True)
        self.provider = fixture.base / "native-provider.json"
        self.provider.write_text('{"fixture_only":true,"grants_lean_proof_credit":false}\n')
        self.qualification = fixture.base / "native-qualification.json"
        self.qualification.write_text('{"fixture_only":true,"grants_lean_proof_credit":false}\n')
        self.path = fixture.base / "native-snapshot.json"
        self.checker = checker or Path(fixture.runner.LEAN)
        (fixture.root / "ImbalancedChen/Mid.lean").write_text(
            "import ImbalancedChen.Dep\nimport MathlibNt.Fixture\n")
        self.write()

    def write(self) -> None:
        def item(path: Path, role: str) -> dict:
            raw = path.read_bytes()
            return {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw), "role": role}
        files = {str(path): item(path, role) for path, role in (
            (self.source, "source"), (self.obj, "object"), (Path(self.fixture.runner.LEAN), "runtime"),
            (self.checker, "runtime"), (self.provider, "provider-receipt"),
            (self.qualification, "qualification-receipt"))}
        raw = self.source.read_bytes()
        row = {"package": "goldbach", "source": str(self.source), "object": str(self.obj),
               "git_blob_sha1": hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest(),
               "imports": [], "dependency_signatures": {},
               "provider": {"status": "FRESH_PRIVATE_SOURCE_COMPILATION", "receipt": str(self.provider)}}
        bound = {key: row[key] for key in ("source", "object", "imports", "dependency_signatures", "provider")}
        bound.update(module="MathlibNt.Fixture", source_sha256=files[str(self.source)]["sha256"],
                     object_sha256=files[str(self.obj)]["sha256"])
        row["closure_signature"] = native_env.signature(bound)
        value = {"schema": native_env.SCHEMA, "status": native_env.STATUS,
                 "compile_credit": False, "kernel_credit": False,
                 "runtime": {"lean": self.fixture.runner.LEAN, "leanchecker": str(self.checker),
                             "mathlib_commit": self.fixture.runner.PIN, "sysroot": str(self.sysroot),
                             "lean_path": [str(self.lib), str(self.sysroot / "lib/lean")]},
                 "packages": {key: {"root": str(self.root), "commit": self.pin} for key in native_env.PINS},
                 "qualification": {"path": str(self.qualification), "sha256": files[str(self.qualification)]["sha256"],
                                   "status": "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED"},
                 "files": files, "modules": {"MathlibNt.Fixture": row},
                 "resolutions": {"MathlibNt.Fixture": str(self.obj)}}
        value["context_signature"] = native_env.signature(value)
        self.path.write_text(json.dumps(value, indent=2) + "\n")

    def args(self) -> list[str]:
        return ["--external-snapshot", str(self.path)]


class NativeCompileBindingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = cache_tests.ProofCacheBindingTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.native = NativeFixture(self.fixture)

    def test_missing_external_snapshot_cannot_adopt_native_context(self) -> None:
        with self.assertRaisesRegex(ValueError, "absent from external snapshot"):
            self.fixture.run_runner()

    def test_prefixed_project_import_cannot_hide_native_ancestry(self) -> None:
        (self.fixture.root / "ImbalancedChen/Page.lean").write_text("public import ImbalancedChen.Mid\n")
        with self.assertRaisesRegex(ValueError, "absent from external snapshot"):
            self.fixture.run_runner()
        self.fixture.run_runner(extra_args=self.native.args())
        self.assertEqual(self.fixture.records()["ImbalancedChen.Page"]["cache_schema"], 3)

    def test_only_actual_native_ancestry_uses_schema_three(self) -> None:
        self.fixture.run_runner(extra_args=self.native.args())
        records = self.fixture.records()
        self.assertEqual(records["ImbalancedChen.Dep"]["cache_schema"], 2)
        self.assertNotIn("external_snapshot", records["ImbalancedChen.Dep"])
        for name in ("ImbalancedChen.Mid", "ImbalancedChen.Page"):
            self.assertEqual(records[name]["cache_schema"], 3)
            self.assertEqual(records[name]["external_check"]["status"], "PASSED_BATCH_PRE_POST")
        self.assertEqual(self.fixture.run_runner(extra_args=self.native.args())["reused"], 3)

    def test_unbound_old_native_records_are_not_upgraded(self) -> None:
        self.fixture.run_runner(extra_args=self.native.args())
        records = self.fixture.records()
        for name in ("ImbalancedChen.Mid", "ImbalancedChen.Page"):
            row = records[name]
            row["cache_schema"] = 2
            row.pop("external_snapshot")
            row.pop("external_check")
            row["dependency_signatures"] = {dep: records[dep]["closure_signature"] for dep in row["deps"]}
            row["closure_signature"] = self.fixture.runner.closure_signature(row)
        self.fixture.write_records(records)
        self.assertEqual(self.fixture.run_runner(extra_args=self.native.args())["reused"], 1)
        self.assertEqual(len(self.fixture.records()["ImbalancedChen.Page"]["attempts"]), 2)

    def test_changed_qualified_native_object_invalidates_ancestors(self) -> None:
        self.fixture.run_runner(extra_args=self.native.args())
        previous = self.fixture.records()["ImbalancedChen.Mid"]["object_sha256"]
        self.native.obj.write_bytes(b"a different independently qualified native fixture")
        self.native.write()
        self.assertEqual(self.fixture.run_runner(extra_args=self.native.args())["reused"], 1)
        self.assertEqual(self.fixture.records()["ImbalancedChen.Mid"]["object_sha256"], previous)

    def test_native_mutation_during_batch_invalidates_all_affected_credit(self) -> None:
        (self.fixture.root / "change-dependency-during-page").write_text(str(self.native.obj))
        result = self.fixture.run_runner(expected_exit=1, extra_args=self.native.args())
        self.assertEqual(result["successful_closure"], 1)
        for name in ("ImbalancedChen.Mid", "ImbalancedChen.Page"):
            row = self.fixture.records()[name]
            self.assertEqual(row["exit_code"], 125)
            self.assertFalse(row["new_strict_compile"])
            self.assertEqual(row["external_check"]["status"], "FAILED_BATCH_POSTCHECK")

    def test_success_is_not_persisted_until_the_batch_postcheck(self) -> None:
        compiler = Path(self.fixture.runner.LEAN)
        compiler.write_text(compiler.read_text() + """
if source.stem == 'Page':
    import json
    row = json.loads(pathlib.Path('.lake/p2-private/records.json').read_text())['ImbalancedChen.Mid']
    assert row['exit_code'] == 125 and row['new_strict_compile'] is False
    assert row['external_check']['status'] == 'PENDING_BATCH_POSTCHECK'
""")
        self.native.write()
        self.fixture.run_runner(extra_args=self.native.args())
        self.assertEqual(self.fixture.records()["ImbalancedChen.Page"]["exit_code"], 0)

    def test_an_earlier_package_root_cannot_shadow_native_object(self) -> None:
        directory = self.fixture.cache / "lib/MathlibNt"
        directory.mkdir(parents=True)
        (directory / "Fixture.olean").write_bytes(b"unqualified earlier object")
        with self.assertRaisesRegex(ValueError, "Actual search root differs"):
            self.fixture.run_runner(extra_args=self.native.args())


class NativeAuditBindingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.audit = audit_tests.PrivateAuditTests()
        self.audit.setUp()
        self.addCleanup(self.audit.doCleanups)
        self.native = NativeFixture(self.audit.fixture, self.audit.checker)
        self.audit.fixture.run_runner(extra_args=self.native.args())

    def test_replay_and_audit_both_bind_the_external_snapshot(self) -> None:
        receipt = self.audit.run_audit(extra_args=self.native.args())
        self.assertTrue(receipt["accepted"])
        self.assertEqual(receipt["replay_binding"]["external_snapshot"], receipt["input_snapshot"]["external_snapshot"])

    def test_native_mutation_during_audit_cannot_earn_acceptance(self) -> None:
        (self.audit.root / "mutate-during-audit").write_text(str(self.native.obj))
        receipt = self.audit.run_audit(expected_exit=1, extra_args=self.native.args())
        self.assertFalse(receipt["accepted"])
        self.assertIn("External physical input changed", receipt["error"])


if __name__ == "__main__":
    unittest.main()
