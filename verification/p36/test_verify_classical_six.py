"""Evidence-gate checks only; this suite never invokes Lean or changes Git state."""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import verify_part3_distribution as validator


def load_wrapper():
    spec = importlib.util.spec_from_file_location(
        "classical_six_wrapper_tests", HERE / "verify_classical_six.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class EvidenceGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.wrapper = load_wrapper()

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.project = self.root / "project"
        self.build = self.project / ".lake/p36-six-core-build"
        self.run = self.build / "runs/fixed-run"
        self.run.mkdir(parents=True)
        self.toolchain = self.root / "toolchain"
        self.audit = b"-- exact unchanged audit fixture\n"
        (self.run / "P36OwnedAudit.lean").write_bytes(self.audit)
        self.records = []
        self.counts = []
        self.report = {
            "status": "VERIFIED_OWNED", "targets": list(self.wrapper.TARGETS),
            "strict_owned": True, "blockers": [], "commands": [], "modules": {},
            "compiler": {"path": str(self.toolchain / "bin/lean")},
            "planned_external_cache_mirrors": ["MathlibNt.Fixture"],
            "external_cache_mirrors": {"MathlibNt.Fixture": {
                "source_objects": {"/cache/MathlibNt/Fixture.olean": "a" * 64},
                "mirrored_objects": {"/build/MathlibNt/Fixture.olean": "a" * 64}}}}
        for name in self.wrapper.TARGETS:
            relative = name.replace(".", "/")
            source = self.project / (relative + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- source fixture\n")
            obj = self.build / "lib/lean" / (relative + ".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            obj.write_bytes(name.encode())
            private = Path(str(obj) + ".private")
            private.write_bytes(b"private fixture")
            command = [str(self.toolchain / "bin/lean"), "-t0", "-j1", "-R",
                       str(self.project), "-DwarningAsError=true", "-o", str(obj), str(source)]
            stage = self.stage("compile-" + name, command, "")
            self.report["modules"][name] = {
                **stage, "action": "compiled", "strict": True,
                "source": str(source), "source_sha256": self.wrapper.sha256(source),
                "objects": {str(p): self.wrapper.sha256(p) for p in (obj, private)}}
            self.records.append({"module": name, "name": name + ".fixture", "kind": "theorem",
                                 "type": "True", "levelParams": [], "axioms": ["propext"]})
            self.counts.append({"module": name, "count": 1})
        for name in self.wrapper.TARGETS:
            self.stage("replay-" + name,
                       [str(self.toolchain / "bin/leanchecker"), "--verbose", name],
                       "replaying " + name + "\n")
        body = "".join("PART3_AUDIT_DECL " + json.dumps(r) + "\n" for r in self.records)
        body += "".join("PART3_AUDIT_MODULE " + json.dumps(r) + "\n" for r in self.counts)
        body += "PART3_AUDIT_COUNT 6\n"
        self.stage("owned-inventory-audit", [str(self.toolchain / "bin/lean"), "-t0", "-j1",
                   "-DwarningAsError=true", "-R", str(self.run), str(self.run / "P36OwnedAudit.lean")], body)
        self.report.update(declaration_count=6, module_counts=self.counts,
                           declarations_file=str(self.run / "declarations.json"))
        (self.run / "declarations.json").write_text(json.dumps(self.records))
        self.runner = SimpleNamespace(report=self.report, run_dir=self.run, project=self.project,
            toolchain=self.toolchain, build=self.build,
            local_object=lambda name: self.build / "lib/lean" / (name.replace(".", "/") + ".olean"))

    def stage(self, name, command, body):
        log = self.run / (name + ".log")
        log.write_text("command=" + json.dumps(command) + "\n" + body)
        stage = {"name": name, "command": command, "exit_code": 0,
                 "log": str(log), "log_sha256": self.wrapper.sha256(log)}
        self.report["commands"].append(stage)
        return stage

    def gate(self, exit_code=0):
        return self.wrapper.validate_completed_run(self.runner, exit_code, validator, self.audit)

    def test_fixed_runner_arguments_and_nonempty_mirrors(self):
        args = argparse.Namespace(project=self.project, packages_dir=None, toolchain_dir=self.toolchain,
                                  build_dir=None, source_manifest=None)
        actual = self.wrapper.make_runner_args(args)
        self.assertEqual(actual.modules, list(self.wrapper.TARGETS))
        self.assertEqual(len(set(actual.modules)), 6)
        self.assertTrue(actual.build and actual.strict_owned and actual.verify_owned)
        self.assertEqual(actual.timeout, 1800)
        self.assertEqual(actual.reuse_verified_bundle, [])
        self.assertEqual(self.gate(), (self.records, self.counts))

    def test_rejects_failed_changed_scope_or_incomplete_stages(self):
        original = copy.deepcopy(self.report)
        cases = [
            lambda r: r.update(status="COMPILED"),
            lambda r: r["targets"].pop(),
            lambda r: r["modules"][self.wrapper.TARGETS[0]].update(action="reused"),
            lambda r: r["modules"][self.wrapper.TARGETS[0]].update(strict=False),
            lambda r: r["commands"].pop(6),
            lambda r: r["commands"].insert(6, copy.deepcopy(r["commands"][6])),
            lambda r: r["commands"][6].update(exit_code=1),
            lambda r: r["commands"][-1].update(exit_code=124),
            lambda r: r["commands"][0]["command"].remove("-DwarningAsError=true"),
        ]
        for mutate in cases:
            with self.subTest(mutation=cases.index(mutate)):
                self.runner.report = copy.deepcopy(original)
                mutate(self.runner.report)
                with self.assertRaises(RuntimeError):
                    self.gate()
        self.runner.report = original
        with self.assertRaises(RuntimeError):
            self.gate(exit_code=1)

    def test_rejects_rehashed_wrong_command_header_and_inexact_replay_line(self):
        stage = self.report["commands"][6]
        log = Path(stage["log"])
        for content in (
            "command=[]\nreplaying " + self.wrapper.TARGETS[0] + "\n",
            "command=" + json.dumps(stage["command"]) + "\nnot replaying " + self.wrapper.TARGETS[0] + "\n",
        ):
            with self.subTest(content=content[:40]):
                log.write_text(content)
                stage["log_sha256"] = self.wrapper.sha256(log)
                with self.assertRaises(RuntimeError):
                    self.gate()

    def test_rejects_inventory_changes_and_missing_or_added_sidecars(self):
        declarations = self.run / "declarations.json"
        declarations.write_text(json.dumps(self.records[:-1]))
        with self.assertRaises(RuntimeError):
            self.gate()
        declarations.write_text(json.dumps(self.records))
        obj = self.runner.local_object(self.wrapper.TARGETS[0])
        private = Path(str(obj) + ".private")
        private.unlink()
        with self.assertRaises(RuntimeError):
            self.gate()
        private.write_bytes(b"private fixture")
        Path(str(obj) + ".server").write_bytes(b"unexpected sidecar")
        with self.assertRaises(RuntimeError):
            self.gate()

    def test_source_identity_requires_exact_head_and_clean_tracked(self):
        with patch.object(self.wrapper, "git", side_effect=["b" * 40, ""]):
            with self.assertRaises(RuntimeError):
                self.wrapper.check_source_identity(self.project, "a" * 40)
        with patch.object(self.wrapper, "git", side_effect=["a" * 40, " M source.lean"]):
            with self.assertRaises(RuntimeError):
                self.wrapper.check_source_identity(self.project, "a" * 40)
        with patch.object(self.wrapper, "git", side_effect=["a" * 40, ""]):
            self.wrapper.check_source_identity(self.project, "a" * 40)

    def test_archive_payload_is_checked_and_receipt_is_published_last(self):
        evidence = self.wrapper.EvidenceArchive()
        source = self.root / "payload"
        source.write_bytes(b"original evidence")
        evidence.add("run/payload", source)
        out = self.root / "evidence"
        out.mkdir()
        def changed_identity():
            raise RuntimeError("HEAD changed after packaging")
        with self.assertRaisesRegex(RuntimeError, "HEAD changed"):
            self.wrapper.publish_evidence(out, evidence, {"status": "VERIFIED_OWNED"}, changed_identity)
        self.assertFalse((out / "RECEIPT.json").exists())
        archive = out / "evidence.tar.xz"
        self.wrapper.verify_archive(archive, evidence.files)
        archive.write_bytes(b"corrupt archive")
        with self.assertRaises(Exception):
            self.wrapper.verify_archive(archive, evidence.files)

    def test_changed_archive_input_cannot_create_a_receipt(self):
        evidence = self.wrapper.EvidenceArchive()
        source = self.root / "payload"
        source.write_bytes(b"original evidence")
        evidence.add("source/payload", source)
        source.write_bytes(b"changed evidence")
        out = self.root / "evidence"
        out.mkdir()
        with self.assertRaises(RuntimeError):
            self.wrapper.publish_evidence(out, evidence, {"status": "VERIFIED_OWNED"}, lambda: None)
        self.assertFalse((out / "RECEIPT.json").exists())


if __name__ == "__main__":
    unittest.main()
