import copy
from argparse import Namespace
from hashlib import sha256
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("export_verified_increment.py")
spec = importlib.util.spec_from_file_location("increment", SCRIPT)
increment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(increment)


class HistoricalRun(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        evidence = SCRIPT.parent.parent / "accepted-classical-six/evidence.tar.xz"
        cls.receipt = json.loads(evidence.with_name("RECEIPT.json").read_bytes())
        with tarfile.open(evidence, "r:xz") as archive:
            cls.payload = {m.name: archive.extractfile(m).read() for m in archive
                           if m.isfile() and (m.name.startswith(("run/", "config/", "source/", "objects/", "lineage/"))
                                              or m.name in {"SOURCE_SELECTION.json", "binding.json"})}
        cls.report = json.loads(cls.payload["run/report.json"])
        cls.run_path = increment.PurePosixPath(cls.report["declarations_file"]).parent
        cls.targets = tuple(cls.report["targets"])
        cls.bodies = increment.stage_bodies(cls.report, cls.run_path, cls.read, cls.targets)
        cls.originals = increment.load_originals(increment.DEFAULT_PROJECT)
        cls.audit_helper = cls.originals[1]
        # The accepted historical archive retains complete state entries and
        # actual prior logs. Recreate minimal prior-report fixtures because it
        # predates retaining the original previous report bytes.
        state = json.loads(cls.payload["lineage/local-state.json"])["modules"]
        prior_reports = {}
        for module, node in cls.report["modules"].items():
            if node["action"] != "reused":
                continue
            old = state[module].copy()
            old["action"] = "compiled"
            directory = increment.lineage_run(cls.run_path, module, node)
            archived = "lineage/runs/" + directory.name + "/" + Path(old["log"]).name
            if directory / "report.json" in increment.LEGACY_REPORT_PINS:
                # This fixture's reconstructed current-writer records must
                # retain distinct paths from the real pinned legacy reports.
                directory = directory.with_name("2025" + directory.name[4:])
                old["log"] = str(directory / Path(old["log"]).name)
                node["previous_log"] = old["log"]
            prior = prior_reports.setdefault(directory.name, {
                key: cls.report[key] for key in ("schema", "project", "build_dir", "runner_sha256")})
            prior["status"] = "FIXTURE"
            prior.setdefault("commands", []).append({key: old[key] for key in (
                "name", "command", "exit_code", "log", "log_sha256")})
            prior.setdefault("modules", {})[module] = old
            prefix = "lineage/" + directory.name
            cls.payload[prefix + "/" + Path(old["log"]).name] = cls.payload[archived]
        for run, prior in prior_reports.items():
            cls.payload["lineage/" + run + "/report.json"] = json.dumps(prior).encode()
        cls.payload["run/report.json"] = json.dumps(cls.report).encode()

    @classmethod
    def read(cls, name, original, digest=None):
        if name in cls.payload:
            data = cls.payload[name]
        elif name.startswith("source/"):
            data = (increment.DEFAULT_PROJECT / name.removeprefix("source/")).read_bytes()
        else:
            raise KeyError(name)
        if digest is not None:
            increment.require(sha256(data).hexdigest() == digest, "Fixture log hash differs")
        return data

    def test_real_complete_historical_inventory(self):
        records, counts = increment.complete_inventory(
            self.report, self.run_path, self.read, self.targets, self.bodies, self.audit_helper)
        self.assertEqual(len(records), 85)
        self.assertEqual(len(counts), 6)

    def test_real_historical_graph(self):
        summary, snapshots, roots, resolved, native = increment.validate_run(
            increment.DEFAULT_PROJECT, self.receipt["source_commit"], self.report,
            self.run_path, self.receipt["source_sha256"], self.read, self.originals)
        self.assertEqual(summary["declaration_count"], 85)
        self.assertEqual(len(roots), 11)
        self.assertEqual(len(resolved), 10_125)
        self.assertEqual(snapshots, json.loads(self.payload["binding.json"])["snapshot_sha256"])
        self.assertTrue(native)
        self.assertEqual(summary["reused_module_count"], 371)
        self.assertEqual(summary["prior_compile_run_count"], 11)
        self.assertEqual({record["writer_binding"] for record in summary["prior_compile_reports"].values()},
                         {"current runner"})
        self.assertIsNone(summary["independent_runtime_binding"]["sha256_before_and_after"])
        self.assertLess(summary["report_recorded_snapshot_count"], summary["snapshot_count"])
        lake_manifest = self.report["project"] + "/lake-manifest.json"
        export_inputs = summary["export_time_additional_input_sha256"]
        self.assertEqual(export_inputs.get(lake_manifest), snapshots[lake_manifest])
        report_only = {path: digest for path, digest in snapshots.items() if path not in export_inputs}
        self.assertEqual(summary["report_recorded_snapshot_count"], len(report_only))
        self.assertEqual(summary["report_recorded_snapshot_sha256"], self.originals[0].digest_json(report_only))
        self.assertEqual(summary["dependency_pins"], self.report["dependency_pins"])
        self.assertEqual(summary["source_selection_binding"], "frozen Git blob")

    def test_refuses_rehashed_mutation_of_frozen_tracked_selection(self):
        # Changing only whitespace keeps every source selection entry and
        # digest valid. A replaced report hash must not override the Git blob.
        data = self.payload["SOURCE_SELECTION.json"] + b"\n"
        manifest = {**self.report["source_manifest"], "sha256": sha256(data).hexdigest()}
        report = {**self.report, "source_manifest": manifest}

        def read(name, original, digest=None):
            if name == "SOURCE_SELECTION.json":
                self.assertEqual(digest, sha256(data).hexdigest())
                return data
            return self.read(name, original, digest)

        with self.assertRaisesRegex(RuntimeError, "Project source differs .*SOURCE_SELECTION.json"):
            increment.validate_run(increment.DEFAULT_PROJECT, self.receipt["source_commit"], report,
                                   self.run_path, self.receipt["source_sha256"], read, self.originals)

    def test_recovered_archive_checks_current_project_sources(self):
        files = {}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive_path = root / "evidence.tar.xz"
            original_report = str(self.run_path / "report.json")
            with tarfile.open(archive_path, "w:xz", preset=1) as archive:
                def capture(name, original, digest=None):
                    data = self.read(name, original, digest)
                    if name not in files:
                        files[name] = {"path": original, "sha256": sha256(data).hexdigest(), "bytes": len(data)}
                        member = tarfile.TarInfo(name)
                        member.size = len(data)
                        archive.addfile(member, io.BytesIO(data))
                    return data

                raw_report = capture("run/report.json", original_report)
                summary, _, _, _, _ = increment.validate_run(
                    increment.DEFAULT_PROJECT, self.receipt["source_commit"], self.report,
                    self.run_path, self.receipt["source_sha256"], capture, self.originals)
            receipt = {**summary, **increment.check_report_identity(sha256(raw_report).hexdigest(), None),
                       "status": "VERIFIED_OWNED_EXPORT", "report_path": original_report,
                       "runtime_binding_file": None, "files": files,
                       "archive_bytes": archive_path.stat().st_size,
                       "archive_sha256": sha256(archive_path.read_bytes()).hexdigest()}
            receipt_path = root / "RECEIPT.json"
            receipt_path.write_text(json.dumps(receipt))
            args = Namespace(receipt=receipt_path, receipt_sha256=sha256(receipt_path.read_bytes()).hexdigest(),
                             archive=archive_path, source_commit=self.receipt["source_commit"])
            result = increment.verify(args, increment.DEFAULT_PROJECT, self.receipt["source_sha256"], self.originals)
            self.assertEqual(result["status"], "PASS_LOCAL_EVIDENCE_VERIFICATION")
            self.assertFalse(result["local_lean_run"])
            self.assertEqual(result["archive_members"], len(files))
            args.receipt_sha256 = "0" * 64
            with self.assertRaisesRegex(RuntimeError, "Pinned receipt"):
                increment.verify(args, increment.DEFAULT_PROJECT, self.receipt["source_sha256"], self.originals)

    def test_refuses_current_source_changed_during_readback(self):
        relative = self.targets[0].replace(".", "/") + ".lean"
        with self.assertRaisesRegex(RuntimeError, "Project source differs"):
            increment.checked_project_source(
                increment.DEFAULT_PROJECT, self.receipt["source_commit"], relative,
                self.payload["source/" + relative] + b"\n")

    def test_refuses_missing_or_unsuccessful_prior_compile(self):
        report = copy.deepcopy(self.report)
        name, node = next((name, node) for name, node in report["modules"].items() if node["action"] == "reused")
        original = node.pop("previous_log")
        with self.assertRaisesRegex(RuntimeError, "Missing previous compile log"):
            increment.capture_lineage(report, self.run_path, self.read)
        node["previous_log"] = original
        records, _ = increment.capture_lineage(report, self.run_path, self.read)
        prior, stage = records[name]
        inputs = {key: prior[key] for key in (
            "source", "source_sha256", "compiler", "strict", "imports", "lean_path", "trust", "threads")}
        increment.check_prior_compile(name, node, (prior, stage), self.run_path, stage["command"], inputs, self.read)
        with self.assertRaisesRegex(RuntimeError, "historical compile differs"):
            increment.check_prior_compile(name, node, ({**prior, "exit_code": 1}, stage),
                                          self.run_path, stage["command"], inputs, self.read)

    def test_legacy_pins_match_independent_diagnostic(self):
        diagnostic = json.loads((SCRIPT.parent / "attempts/lineage-diagnostic.json").read_bytes())
        expected = {}
        for run in diagnostic:
            for previous in run["prior_runs"]:
                if "runner_sha256" in previous["mismatches"]:
                    path = increment.PurePosixPath(previous["path"])
                    pin = (previous["runner_sha256"], previous["sha256"])
                    self.assertEqual(expected.get(path, pin), pin)
                    expected[path] = pin
        self.assertEqual(len(expected), 16)
        self.assertEqual(increment.LEGACY_REPORT_PINS, expected)

    def test_pinned_legacy_writer_still_requires_an_exact_successful_compile(self):
        name, node = next((name, node) for name, node in self.report["modules"].items() if node["action"] == "reused")
        current = {**self.report, "modules": {name: node}}
        directory = increment.lineage_run(self.run_path, name, node)
        path = directory / "report.json"
        member = "lineage/" + directory.name + "/report.json"
        earlier = json.loads(self.payload[member])
        earlier["status"] = "FAILED"
        writer = next(iter(increment.LEGACY_REPORT_PINS.values()))[0]
        earlier["runner_sha256"] = writer
        raw = json.dumps(earlier).encode()

        def read(archive_name, original, digest=None):
            return raw if archive_name == member else self.read(archive_name, original, digest)

        def extract():
            return increment.capture_lineage(current, self.run_path, read)

        with self.assertRaisesRegex(RuntimeError, "Unpinned historical runner"):
            extract()
        with patch.dict(increment.LEGACY_REPORT_PINS, {path: (writer, sha256(raw).hexdigest())}):
            lineage, reports = extract()
            old, stage = lineage[name]
            self.assertEqual(reports[str(path)]["status"], "FAILED")
            self.assertEqual(reports[str(path)]["writer_binding"], "pinned legacy report")
            inputs = {key: old[key] for key in (
                "source", "source_sha256", "compiler", "strict", "imports", "lean_path", "trust", "threads")}
            increment.check_prior_compile(name, node, (old, stage), self.run_path, stage["command"], inputs, read)
            original = raw
            raw += b"\n"
            with self.assertRaisesRegex(RuntimeError, "Pinned legacy compile report writer or SHA-256"):
                extract()
            raw = original
        with patch.dict(increment.LEGACY_REPORT_PINS, {path: ("0" * 64, sha256(raw).hexdigest())}):
            with self.assertRaisesRegex(RuntimeError, "Pinned legacy compile report writer or SHA-256"):
                extract()

        earlier["modules"][name]["exit_code"] = 1
        next(stage for stage in earlier["commands"] if stage["name"] == "compile-" + name)["exit_code"] = 1
        raw = json.dumps(earlier).encode()
        with patch.dict(increment.LEGACY_REPORT_PINS, {path: (writer, sha256(raw).hexdigest())}):
            lineage, _ = extract()
            with self.assertRaisesRegex(RuntimeError, "historical compile differs"):
                increment.check_prior_compile(name, node, lineage[name], self.run_path, stage["command"], inputs, read)

    def test_refuses_compile_replay_reordering(self):
        increment.check_stage_order(self.report, self.targets)
        report = copy.deepcopy(self.report)
        stages = report["commands"]
        compile_at = next(i for i, stage in enumerate(stages) if stage["name"] == "compile-" + self.targets[0])
        replay_at = next(i for i, stage in enumerate(stages) if stage["name"] == "replay-" + self.targets[0])
        stages[compile_at], stages[replay_at] = stages[replay_at], stages[compile_at]
        with self.assertRaisesRegex(RuntimeError, "audit order differs"):
            increment.check_stage_order(report, self.targets)

    def test_refuses_invalid_selection_manifest(self):
        runner, project = self.originals[0], increment.DEFAULT_PROJECT
        commit = self.receipt["source_commit"]
        manifest = json.loads(self.payload["SOURCE_SELECTION.json"])
        self.assertEqual(increment.check_source_manifest(
            self.payload["SOURCE_SELECTION.json"], self.report, project, commit, runner), 377)
        with self.assertRaisesRegex(RuntimeError, "missing its sources"):
            increment.check_source_manifest(b"{}", self.report, project, commit, runner)
        manifest["sources"][0]["selected_path"] = "../wrong.lean"
        with self.assertRaisesRegex(RuntimeError, "Selected source path"):
            increment.check_source_manifest(
                json.dumps(manifest).encode(), self.report, project, commit, runner)

    def test_refuses_external_source_outside_package_and_missing_native_alias(self):
        objdir = increment.absolute(self.report["build_dir"]) / "lib/lean"
        roots = increment.check_environment(self.report, self.bodies, objdir, self.report["dependency_pins"],
                                            self.originals[0])
        with self.assertRaisesRegex(RuntimeError, "escapes its pinned package"):
            increment.check_external_source({"source": "/different/Mathlib/Init.lean"},
                                            "mathlib", "cached", "Mathlib/Init.lean", roots)
        listing = self.bodies["native-tracked-files"]
        relative = next(line.split("\t")[1] for line in listing.splitlines()
                        if line.split("\t")[1].startswith("research/wu2008/src/MathlibNt/Wu2008DoubleSieve/")
                        and line.endswith(".lean"))
        flat = relative.removeprefix("research/wu2008/src/")
        native = flat.removesuffix(".lean").replace("/", ".")
        node = {"package": "goldbach", "source": str(roots["goldbach"] / flat), "source_sha256": "0" * 64}
        report = {**self.report, "modules": {native: node}}
        with self.assertRaisesRegex(RuntimeError, "alias records differ"):
            increment.check_native_sources(report, self.bodies, roots, {})
        report["native_research_aliases"] = [{
            "module": native, "source": node["source"], "sha256": node["source_sha256"],
            "tracked_matches": [{"path": relative, "git_blob":
                                 next(line.split()[1] for line in listing.splitlines()
                                      if line.endswith("\t" + relative))}],
        }]
        self.assertIn(node["source"], increment.check_native_sources(report, self.bodies, roots, {}))

    def test_runtime_binding_and_terminal_hash_are_separate(self):
        owner = self.targets[0]
        commit = self.receipt["source_commit"]
        run_report = str(self.run_path / "report.json")
        report_sha = sha256(self.payload["run/report.json"]).hexdigest()
        tool_hashes = {self.report["compiler"]["path"]: increment.COMPILER_SHA256,
                       self.report["compiler"]["path"] + "checker": increment.CHECKER_SHA256}
        evidence = {"owner": owner, "source_commit": commit, "status": "VERIFIED_OWNED", "exit_code": 0,
                    "report": run_report, "report_sha256": report_sha,
                    "runtime_tool_sha256_before": tool_hashes, "runtime_tool_sha256_after": tool_hashes}
        binding = {"path": "/original/runtime.json", "sha256": "0" * 64}
        args = (binding, run_report, report_sha, commit, (owner,), tool_hashes)
        read = lambda *unused: json.dumps(evidence).encode()
        self.assertEqual(increment.check_runtime_binding(read, *args)["status"], "independently captured")
        evidence["runtime_tool_sha256_after"] = {}
        with self.assertRaisesRegex(RuntimeError, "Independent runtime binding differs"):
            increment.check_runtime_binding(read, *args)
        with self.assertRaisesRegex(RuntimeError, "pinned terminal digest"):
            increment.check_report_identity(report_sha, "0" * 64)

    def test_tampered_archive_helpers_are_never_imported(self):
        for relative in increment.HELPER_DIGESTS:
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                for name in increment.HELPER_DIGESTS:
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    content = (increment.DEFAULT_PROJECT / "verification/p36" / name).read_bytes()
                    path.write_bytes(content if name != relative else b"raise SystemExit(123)\n")
                with self.assertRaisesRegex(RuntimeError, "differs before import"):
                    increment.load_originals(increment.DEFAULT_PROJECT, root)

    def test_refuses_failed_run_and_missing_exact_replay(self):
        report = copy.deepcopy(self.report)
        report["status"] = "FAILED"
        with self.assertRaisesRegex(RuntimeError, "VERIFIED_OWNED"):
            increment.stage_bodies(report, self.run_path, self.read, self.targets)
        bodies = self.bodies.copy()
        replay = "replay-" + self.targets[0]
        bodies[replay] = bodies[replay].replace("replaying " + self.targets[0], "replaying Wrong.Module")
        with self.assertRaisesRegex(RuntimeError, "replay line"):
            increment.exact_owned_stages(self.report, self.run_path, self.targets, bodies)

    def test_refuses_wrong_owner_and_tampered_log(self):
        with self.assertRaisesRegex(RuntimeError, "VERIFIED_OWNED"):
            increment.stage_bodies(self.report, self.run_path, self.read, ("Wrong.Module",))
        report = copy.deepcopy(self.report)
        report["commands"][0]["log_sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError, "log hash"):
            increment.stage_bodies(report, self.run_path, self.read, self.targets)

    def test_refuses_weakened_strict_command(self):
        report = copy.deepcopy(self.report)
        name = self.targets[0]
        stage = next(s for s in report["commands"] if s["name"] == "compile-" + name)
        stage["command"].remove("-DwarningAsError=true")
        report["modules"][name]["command"] = stage["command"]
        with self.assertRaisesRegex(RuntimeError, "strict compile"):
            increment.exact_owned_stages(report, self.run_path, self.targets, self.bodies)

    def test_refuses_forbidden_axiom_and_missing_declarations(self):
        bodies = self.bodies.copy()
        audit = "owned-inventory-audit"
        bodies[audit] = bodies[audit].replace('"propext"', '"sorryAx"', 1)
        with self.assertRaisesRegex(RuntimeError, "Invalid declaration"):
            increment.complete_inventory(
                self.report, self.run_path, self.read, self.targets, bodies, self.audit_helper)
        lines = self.bodies[audit].splitlines()
        lines.pop(next(i for i, line in enumerate(lines) if line.startswith("PART3_AUDIT_DECL ")))
        bodies[audit] = "\n".join(lines)
        with self.assertRaisesRegex(RuntimeError, "inconsistent declaration"):
            increment.complete_inventory(
                self.report, self.run_path, self.read, self.targets, bodies, self.audit_helper)

    def test_refuses_object_sidecar_outside_expected_set(self):
        base = "/original/lib/lean/ImbalancedChen/Owner.olean"
        for objects in ({base + ".private": "0" * 64}, {base: "0" * 64, base + ".other": "0" * 64}):
            with self.subTest(objects=objects), self.assertRaisesRegex(RuntimeError, "sidecar"):
                increment.check_object_facets(base, objects)

    def test_refuses_tar_bad_member_type_or_hash(self):
        payload = self.payload["run/P36OwnedAudit.lean"]
        files = {"run/P36OwnedAudit.lean": {
            "path": str(self.run_path / "P36OwnedAudit.lean"), "sha256": sha256(payload).hexdigest(),
            "bytes": len(payload)}}
        for symlink in (False, True):
            with self.subTest(symlink=symlink), tempfile.TemporaryDirectory() as temporary:
                output = io.BytesIO()
                with tarfile.open(fileobj=output, mode="w:xz") as archive:
                    info = tarfile.TarInfo("run/P36OwnedAudit.lean")
                    if symlink:
                        info.type = tarfile.SYMTYPE
                        info.linkname = "/nonexistent"
                        archive.addfile(info)
                    else:
                        info.size = len(payload)
                        archive.addfile(info, io.BytesIO(b"X" + payload[1:]))
                with self.assertRaisesRegex(RuntimeError, "Nonregular|hash differ"):
                    self.originals[2].safe_unpack(output.getvalue(), files, Path(temporary))


if __name__ == "__main__":
    unittest.main()
