import copy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path, PurePosixPath
import tempfile
import unittest

from export_group_evidence import (
    OWNERS, PINNED_PREVIOUS_SHA256, check_runtime_binding, group_receipt,
    PREVIOUS, ROOT_Q_LEGACY_PIN, load_previous, parse_owner_manifest,
)


def encoded(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def digest(value):
    return sha256(value).hexdigest()


class GroupBinding(unittest.TestCase):
    def setUp(self):
        self.commit = "1" * 40
        self.report_path = "/workspace/project/.lake/p36-build/runs/20261126T040000.000000Z/report.json"
        self.report_sha = "2" * 64
        self.sources = [{
            "module": owner,
            "selected_path": owner.replace(".", "/") + ".lean",
            "selected_sha256": digest(owner.encode()),
        } for owner in OWNERS]
        self.manifest = encoded({"sources": self.sources})
        self.manifest_identity = {"path": "/workspace/project/FROZEN_SOURCES.json", "sha256": digest(self.manifest)}
        self.owners = {entry["module"]: entry["selected_sha256"] for entry in self.sources}
        self.tools = {
            "/toolchain/bin/lean": "3" * 64,
            "/toolchain/bin/leanchecker": "4" * 64,
            "/workspace/project/verification/p36/compile_p36_local.py": "5" * 64,
            "/workspace/project/verification/verify_part3_continuation.py": "6" * 64,
            "/workspace/project/verification/verify_part3_distribution.py": "7" * 64,
            "/workspace/project/verification/Part3DistributionAudit.lean": "8" * 64,
        }
        self.binding = {
            "owners": list(OWNERS), "source_commit": self.commit,
            "status": "VERIFIED_OWNED", "exit_code": 0, "report": self.report_path,
            "report_sha256": self.report_sha, "source_manifest": self.manifest_identity,
            "runtime_tool_sha256_before": self.tools, "runtime_tool_sha256_after": self.tools,
        }

    def check(self, binding):
        return check_runtime_binding(
            binding, self.commit, self.owners, self.report_path, self.report_sha,
            self.manifest_identity, self.tools)

    def test_exact_ordered_manifest_and_hash(self):
        self.assertEqual(list(parse_owner_manifest(self.manifest, digest(self.manifest))), list(OWNERS))
        with self.assertRaisesRegex(RuntimeError, "manifest SHA-256"):
            parse_owner_manifest(self.manifest + b" ", digest(self.manifest))
        changes = (
            self.sources[:-1], self.sources + [self.sources[0]],
            self.sources[::-1], self.sources[:-1] + [{**self.sources[-1], "module": "ImbalancedChen.Wrong"}],
        )
        for sources in changes:
            with self.subTest(sources=[entry["module"] for entry in sources]):
                raw = encoded({"sources": sources})
                with self.assertRaisesRegex(RuntimeError, "exact ordered owner"):
                    parse_owner_manifest(raw, digest(raw))
        raw = encoded({"sources": [*self.sources[:-1], {**self.sources[-1], "selected_path": "../bad.lean"}]})
        with self.assertRaisesRegex(RuntimeError, "Owner source path or hash"):
            parse_owner_manifest(raw, digest(raw))

    def test_runtime_binding_exact_owner_order_and_stage_identity(self):
        self.check(self.binding)
        for field, value in (
            ("owners", list(OWNERS[:-1])), ("owners", [*OWNERS, OWNERS[0]]),
            ("owners", list(reversed(OWNERS))), ("report_sha256", "0" * 64),
            ("source_manifest", {**self.manifest_identity, "sha256": "0" * 64}),
            ("runtime_tool_sha256_after", {**self.tools, "/toolchain/bin/leanchecker": "0" * 64}),
            ("runtime_tool_sha256_after", dict(list(self.tools.items())[:-1])),
            ("exit_code", False), ("status", "FAILED"), ("source_commit", "0" * 40),
        ):
            with self.subTest(field=field, value=value), self.assertRaisesRegex(RuntimeError, "Group runtime binding differs"):
                self.check({**self.binding, field: value})

    def test_group_receipt_binds_archive_receipt_source_and_runtime_without_relabeling_base(self):
        original = {
            "status": "VERIFIED_OWNED_EXPORT", "whole_p36_closed": False,
            "targets": list(OWNERS), "source_commit": self.commit, "source_sha256": self.owners,
            "report_path": self.report_path, "report_sha256": self.report_sha,
            "terminal_report_sha256": self.report_sha,
            "archive_sha256": "9" * 64, "archive_bytes": 123,
            "files": {"SOURCE_SELECTION.json": {**self.manifest_identity, "bytes": len(self.manifest)}},
            "prior_compile_reports": {},
            "runtime_binding_file": None,
            "independent_runtime_binding": {"status": "unknown", "sha256_before_and_after": None},
        }
        binding_raw = encoded(self.binding)
        receipt_raw = encoded(original)
        result = group_receipt(receipt_raw, self.manifest, binding_raw, self.commit, self.owners, self.binding)
        self.assertEqual(result["base_receipt_sha256"], digest(receipt_raw))
        self.assertEqual(result["archive_sha256"], original["archive_sha256"])
        self.assertEqual(result["runtime_binding_sha256"], digest(binding_raw))
        self.assertEqual(result["additional_root_q_legacy_report"], {**ROOT_Q_LEGACY_PIN, "used": False})
        self.assertFalse(result["whole_p36_closed"])
        self.assertFalse(result["currentVerified"])
        self.assertEqual(original["independent_runtime_binding"]["status"], "unknown")
        bad_owner_hashes = {**self.owners, OWNERS[-1]: "0" * 64}
        with self.assertRaisesRegex(RuntimeError, "Base receipt group identity differs"):
            group_receipt(encoded({**original, "source_sha256": bad_owner_hashes}), self.manifest, binding_raw,
                          self.commit, self.owners, self.binding)

    def test_group_receipt_bounds_additional_report_to_root_q_dependency(self):
        pin = ROOT_Q_LEGACY_PIN
        report = PurePosixPath(pin["report_path"])
        prefix = "lineage/" + report.parent.name + "/"
        root_q_log = prefix + "compile-" + pin["module"] + ".log"
        lineage = {"runner_sha256": pin["runner_sha256"], "report_sha256": pin["report_sha256"],
                   "status": "FAILED", "writer_binding": "pinned legacy report", "reused_module_count": 1}
        original = {
            "status": "VERIFIED_OWNED_EXPORT", "whole_p36_closed": False,
            "targets": list(OWNERS), "source_commit": self.commit, "source_sha256": self.owners,
            "report_path": self.report_path, "report_sha256": self.report_sha,
            "terminal_report_sha256": self.report_sha, "archive_sha256": "9" * 64, "archive_bytes": 123,
            "files": {
                "SOURCE_SELECTION.json": {**self.manifest_identity, "bytes": len(self.manifest)},
                prefix + "report.json": {"path": str(report), "sha256": pin["report_sha256"], "bytes": 13762383},
                root_q_log: {},
            },
            "prior_compile_reports": {str(report): lineage},
            "runtime_binding_file": None,
            "independent_runtime_binding": {"status": "unknown", "sha256_before_and_after": None},
        }

        def make_receipt(base):
            return group_receipt(encoded(base), self.manifest, encoded(self.binding), self.commit, self.owners,
                                 self.binding)

        self.assertEqual(make_receipt(original)["additional_root_q_legacy_report"], {**pin, "used": True})
        mutated = copy.deepcopy(original)
        mutated["prior_compile_reports"][str(report)]["report_sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError, "RootQ dependency lineage differs"):
            make_receipt(mutated)
        mutated = copy.deepcopy(original)
        mutated["files"][prefix + "compile-ImbalancedChen.Other.log"] = mutated["files"].pop(root_q_log)
        with self.assertRaisesRegex(RuntimeError, "RootQ dependency lineage differs"):
            make_receipt(mutated)

    def test_previous_exporter_bytes_pinned_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            bad = Path(directory) / "export_verified_increment.py"
            bad.write_text("raise SystemExit(91)\n")
            with self.assertRaisesRegex(RuntimeError, "Previous exporter SHA-256"):
                load_previous(bad)
        self.assertEqual(digest(Path(load_previous().__file__).read_bytes()), PINNED_PREVIOUS_SHA256)


class InheritedMultiOwnerEvidence(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        script = Path(__file__).resolve().parent.parent / "normalized-density/test_export_verified_increment.py"
        spec = importlib.util.spec_from_file_location("admission_historical_fixture", script)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        cls.fixture = module.HistoricalRun
        cls.fixture.setUpClass()
        # This test's accepted historical fixture reconstructs prior report
        # shells. Use the unmodified exporter for that older manifest.
        cls.previous = module.increment

    def test_classical_archive_reuses_full_guard_and_rejects_stage_omission(self):
        fixture = self.fixture
        args = (self.previous.DEFAULT_PROJECT, fixture.receipt["source_commit"], fixture.report,
                fixture.run_path, fixture.receipt["source_sha256"], fixture.read, fixture.originals)
        summary, snapshots, _, resolved, _ = self.previous.validate_run(*args)
        self.assertEqual(len(summary["targets"]), 6)
        self.assertEqual(summary["declaration_count"], 85)
        self.assertEqual(len(snapshots), 37_857)
        self.assertEqual(len(resolved), 10_125)
        bad = copy.deepcopy(fixture.report)
        first_replay = "replay-" + fixture.targets[0]
        bad["commands"] = [stage for stage in bad["commands"] if stage["name"] != first_replay]
        with self.assertRaisesRegex(RuntimeError, "Kernel replay owner set differs"):
            self.previous.validate_run(*args[:2], bad, *args[3:])


class RootQLegacyPin(unittest.TestCase):
    def test_extends_exact_pin_map_using_the_independent_readout(self):
        previous = load_previous()
        original = PREVIOUS.read_bytes()
        self.assertEqual(digest(original), PINNED_PREVIOUS_SHA256)
        spec = importlib.util.spec_from_file_location("p36_unextended_exporter_fixture", PREVIOUS)
        base = importlib.util.module_from_spec(spec)
        exec(compile(original, str(PREVIOUS), "exec"), base.__dict__)
        readout_path = Path(__file__).resolve().parent / "validation/ROOT_Q_LEGACY_READOUT.jsonl"
        records = [json.loads(line) for line in readout_path.read_text().splitlines()]
        raw, = [record for record in records if record["path"] == ROOT_Q_LEGACY_PIN["report_path"]]
        path = PurePosixPath(raw["path"])
        self.assertEqual((raw["writer"], raw["sha256"]),
                         (ROOT_Q_LEGACY_PIN["runner_sha256"], ROOT_Q_LEGACY_PIN["report_sha256"]))
        self.assertNotIn(path, base.LEGACY_REPORT_PINS)
        self.assertEqual(previous.LEGACY_REPORT_PINS, {**base.LEGACY_REPORT_PINS, path: (raw["writer"], raw["sha256"])})
        self.assertEqual(raw["status"], "FAILED")
        self.assertEqual(raw["rootQ_module"]["exit_code"], 0)
        self.assertEqual(raw["rootQ_module"]["action"], "compiled")

    def test_rejects_changed_legacy_report_and_unknown_old_writer(self):
        previous = load_previous()
        path = PurePosixPath(ROOT_Q_LEGACY_PIN["report_path"])
        build = path.parents[2]
        run = build / "runs/20261126T050000.000000Z"
        module = ROOT_Q_LEGACY_PIN["module"]
        original = {"schema": 1, "project": str(build.parents[1]), "build_dir": str(build),
                    "runner_sha256": "be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709"}
        for directory, writer, error in (
            (path.parent, ROOT_Q_LEGACY_PIN["runner_sha256"], "Pinned legacy compile report writer or SHA-256 differs"),
            (path.parent, "0" * 64, "Pinned legacy compile report writer or SHA-256 differs"),
            (path.parent, original["runner_sha256"], "Pinned legacy compile report writer or SHA-256 differs"),
            (path.parent.with_name("20261125T151945.477149Z"), ROOT_Q_LEGACY_PIN["runner_sha256"],
             "Unpinned historical runner"),
        ):
            with self.subTest(directory=directory, writer=writer), self.assertRaisesRegex(RuntimeError, error):
                report = {**original, "modules": {module: {"action": "reused",
                    "previous_log": str(directory / ("compile-" + module + ".log"))}}}
                changed_bytes = encoded({**original, "runner_sha256": writer, "status": "FAILED"})
                previous.capture_lineage(report, run, lambda *unused: changed_bytes)


if __name__ == "__main__":
    unittest.main()
