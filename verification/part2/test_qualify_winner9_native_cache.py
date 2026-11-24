"""Private receiver regression tests; synthetic bytes provide no Lean credit."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import zipfile

import qualify_winner9_native_cache as receiver
import repack_winner9_native_cache as carrier
from test_repack_winner9_native_cache import Fixture


class ReceiverTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        fixture = Fixture()
        template = json.loads(Path(__file__).with_name("winner9_native_cache_request.json").read_text())
        projects = carrier.ROOTS + [f"ImbalancedChen.Fixture{i:03}" for i in range(242)]
        natives = [f"MathlibNt.Fixture{i:02}" for i in range(21)]
        names, requested = projects + natives + ["Architect.Command"], {}
        for name in names:
            imports = names[1:] if name == names[0] else ["Mathlib.Data.Nat.Basic"]
            raw = ("\n".join("import " + dep for dep in imports) + "\n").encode()
            requested[name] = {"package": carrier.package_for(name), "source_path": name.replace(".", "/") + ".lean",
                               "source_sha256": carrier.digest(raw), "source_bytes": len(raw),
                               "git_blob_sha1": carrier.blob_sha(raw), "direct_imports": imports}
            if name in (names[0], natives[0], "Architect.Command"):
                fixture.module(name, raw, carrier.ARCHITECT_QUARANTINE if name == "Architect.Command" else None)
        fixture.cp["packages"] = [{"name": name, **row, "pin_matches": True, "tracked_sources_clean": True}
                                  for name, row in template["locked_packages"].items()]
        self.census = self.root / "census.json"
        self.census.write_text('{"synthetic_receiver_fixture":true}\n')
        request = {**template, "status": carrier.READY, "requested": requested, "direct_native_roots": natives,
                   "source_census": {"sha256": carrier.file_sha(self.census), "script_sha256": carrier.CENSUS_SCRIPT_SHA,
                                     "status": "SOURCE_GRAPH_COMPLETE_CACHE_ACCEPTANCE_PENDING",
                                     "project_source_count": 247, "native_source_count": 22}}
        archive = self.root / "original.zip"
        cp_raw = carrier.encoded(fixture.cp)
        with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_STORED) as output:
            carrier.zip_write(output, "CHECKPOINT.json", cp_raw)
            for key, raw in fixture.payloads.items():
                carrier.zip_write(output, key, raw)
        anchor = {**carrier.ARTIFACT, "bytes": archive.stat().st_size, "sha256": carrier.file_sha(archive),
                  "checkpoint_bytes": len(cp_raw), "checkpoint_sha256": carrier.digest(cp_raw)}
        request["artifact"] = anchor
        self.request = self.root / "request.json"
        self.request.write_bytes(carrier.encoded(request))
        metadata = self.root / "metadata.json"
        metadata.write_bytes(carrier.encoded({"id": anchor["id"], "expired": False,
            "size_in_bytes": anchor["bytes"], "digest": "sha256:" + anchor["sha256"],
            "workflow_run": {"id": anchor["run_id"], "head_sha": anchor["producer_commit"]}}))
        patcher = patch.object(carrier, "ARTIFACT", anchor)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.packets = self.root / "packets"
        with contextlib.redirect_stdout(io.StringIO()):
            carrier.repack(archive, self.request, metadata, self.packets)
        self.args = SimpleNamespace(packets=self.packets, request=self.request, census=self.census, out=self.root / "stage")
        self.fixture = fixture

    def test_receiver_preserves_original_quarantine_and_all_payload_bytes(self) -> None:
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(receiver.stage(self.args), 0)
        staged = receiver.read(self.args.out / "STAGED.json")
        self.assertEqual(staged["status"], "BYTES_ONLY_NOT_QUALIFIED")
        self.assertFalse(staged["compile_credit"])
        self.assertFalse(staged["kernel_credit"])
        manifest = receiver.read(self.args.out / "EXPORT_MANIFEST.json")
        self.assertEqual(manifest["selected_modules"]["Architect.Command"]["original_classification"], carrier.ARCHITECT_QUARANTINE)
        for name, row in manifest["selected_modules"].items():
            for facet in row["facets"]:
                path = receiver.staged_facet(self.args.out, row["package"], name, facet["original_path"], self.fixture.cp["runtime_state"]["root"])
                self.assertEqual(path.read_bytes(), self.fixture.payloads[facet["payload"]])

    def test_changed_packet_cannot_reach_staging_acceptance(self) -> None:
        path = self.packets / "part-001.zip"
        path.write_bytes(path.read_bytes() + b"transport corruption")
        with self.assertRaisesRegex(ValueError, "Packet transport bytes changed"):
            receiver.stage(self.args)
        self.assertFalse((self.args.out / "STAGED.json").exists())

    def test_exporter_metadata_cannot_upgrade_original_quarantine(self) -> None:
        path = self.packets / "part-000.zip"
        with zipfile.ZipFile(path) as packet:
            data = {name: packet.read(name) for name in packet.namelist()}
        manifest = json.loads(data["EXPORT_MANIFEST.json"])
        manifest["selected_modules"]["Architect.Command"]["original_classification"] = carrier.CLASSIFIED
        data["EXPORT_MANIFEST.json"] = carrier.encoded(manifest)
        path.unlink()
        with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_STORED) as packet:
            for name, raw in data.items():
                carrier.zip_write(packet, name, raw)
        with self.assertRaisesRegex(ValueError, "Byte selection differs"):
            receiver.stage(self.args)

    def test_existing_different_output_is_never_overwritten(self) -> None:
        path = self.root / "existing.olean"
        path.write_bytes(b"existing")
        with self.assertRaisesRegex(ValueError, "must not be overwritten"):
            receiver.atomic_missing(path, b"another object", carrier.digest(b"another object"))
        self.assertEqual(path.read_bytes(), b"existing")

    def test_external_artifact_mapping_rejects_native_executable(self) -> None:
        qualifier = receiver.Qualification.__new__(receiver.Qualification)
        qualifier.cp = {"actual_import_sources": {"MathlibNt.Fixture": {"package": "goldbach", "source": {}}}}
        qualifier.request = {"requested": {"MathlibNt.Fixture": {}}}
        qualifier.active = self.root / "active"
        self.assertEqual(qualifier.current_artifact("MathlibNt.Fixture", "/old/MathlibNt/Fixture.olean"),
                         self.root / "active/MathlibNt/Fixture.olean")
        with self.assertRaisesRegex(ValueError, "Unreviewed actual import artifact kind"):
            qualifier.current_artifact("MathlibNt.Fixture", "/old/MathlibNt/Fixture.so")


class BatteriesOverlayTests(unittest.TestCase):
    """The real restoration gate, with synthetic CP inputs and no Lean process."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.fixture = Fixture()
        self.donor = self.root / "cached-batteries"
        (self.donor / ".git").mkdir(parents=True)
        self.baseline = self.root / "baseline-batteries"
        self.pin = "b" * 40
        self.payloads = {}
        # Include the umbrella module: its five files are Batteries.* beside
        # the namespace directory, not paths containing /Batteries/.
        self.modules = ["Batteries", "Batteries.Tactic.Lemma", "Batteries.Util.Pickle"]
        old = self.fixture.cp["runtime_state"]["root"] + "/.lake/packages/batteries/"
        for name in [*self.modules, "Batteries.Unrequested"]:
            relative = name.replace(".", "/")
            raw = ("module\nprelude\n-- synthetic " + name + "\n").encode()
            record = self.fixture.record(old + relative + ".lean", raw)
            self.fixture.cp["actual_import_sources"][name] = {"package": "batteries", "source": record}
            for root in (self.baseline, self.donor):
                source = root / (relative + ".lean")
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_bytes(raw)
            for suffix in receiver.LOAD_SUFFIXES:
                target = relative + suffix
                raw = (name + ":synthetic:" + suffix).encode()
                self.payloads[target] = raw
                self.fixture.record(old + ".lake/build/lib/lean/" + target, raw)
                path = self.donor / ".lake/build/lib/lean" / target
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
        requested = {}
        setup_rows = []
        for name, imports in [("MathlibNt.Required", self.modules[:1]),
                              ("ImbalancedChen.Required", self.modules)]:
            row, wanted = self.fixture.module(name)
            requested[name] = wanted
            arts = {dep: [[old + ".lake/build/lib/lean/" + dep.replace(".", "/") + suffix
                           for suffix in receiver.LOAD_SUFFIXES]] for dep in imports}
            setup = {"name": name, "package": "imbalancedChen" if wanted["package"] == "project" else wanted["package"],
                     "options": {}, "plugins": [], "dynlibs": [], "isModule": True, "importArts": arts}
            old_setup = row["setup"]
            row["setup"] = self.fixture.record(old_setup["original_path"], carrier.encoded(setup))
            row["facet_files"] = [row["setup"] if item is old_setup else item for item in row["facet_files"]]
            original_map = {dep: [[path, self.fixture.cp["files"][path]["sha256"]]
                                 for group in groups for path in group] for dep, groups in arts.items()}
            row["actual_import_map_sha256"] = receiver.signature(original_map)
            setup_rows.append((name, wanted["package"], row["setup"]))
        q = receiver.Qualification.__new__(receiver.Qualification)
        q.stage = self.root / "stage"
        q.active = q.stage / "active/lib"
        q.active.mkdir(parents=True)
        q.project = self.root / "project"
        q.project.mkdir()
        q.private_lib = q.project / ".lake/p2-private/lib"
        q.request = {"requested": requested, "locked_packages": {"batteries": {"rev": self.pin}}}
        q.cp = self.fixture.cp
        q.selected, _, _, _ = carrier.select_payloads(q.cp, q.request)
        q.packages = {"batteries": self.baseline}
        q.hashes, q.bound, q.resolutions, q.qualified = receiver.PhysicalHashes(), {}, {}, {}
        q.batteries_overlay, q.batteries_donor = {}, None
        q.paths = [q.active, self.baseline / ".lake/build/lib/lean", self.root / "toolchain/lib/lean"]
        q.toolchain = self.root / "toolchain"
        q.lean = q.toolchain / "bin/lean"
        q.env = {"LEAN_PATH": ":".join(map(str, q.paths)), "LEAN_SYSROOT": str(q.toolchain)}
        q.producer_copy = q.stage / "synthetic-producer.py"
        q.producer_copy.write_text("# No compiler or theorem acceptance in this fixture.\n")
        (q.stage / "REQUEST.json").write_bytes(carrier.encoded(q.request))
        for name, package, row in setup_rows:
            path = receiver.staged_facet(q.stage, package, name, row["original_path"], q.cp["runtime_state"]["root"])
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(self.fixture.payloads[row["payload"]])
        self.q = q

        def git_query(command, *, cwd, **_kwargs):
            self.assertEqual(Path(cwd), self.donor)
            if command == ["git", "rev-parse", "HEAD"]:
                return self.pin + "\n"
            if command == ["git", "diff", "HEAD", "--"]:
                return b""
            raise AssertionError("Unexpected donor command: " + str(command))

        patcher = patch.object(receiver.subprocess, "check_output", side_effect=git_query)
        patcher.start()
        self.addCleanup(patcher.stop)

    def receipt(self) -> Path:
        return self.q.stage / "standard-input-overlays/batteries.json"

    def test_complete_required_union_repairs_partial_overlay_without_changing_roots(self) -> None:
        first = "Batteries/Tactic/Lemma.olean"
        path = self.q.active / first
        path.parent.mkdir(parents=True)
        path.write_bytes(self.payloads[first])
        env, paths = dict(self.q.env), list(self.q.paths)
        self.q.restore_batteries(self.donor)
        self.assertEqual(self.q.env, env)
        self.assertEqual(self.q.paths, paths)
        self.assertEqual(self.q.qualified, {})
        for name in self.modules:
            self.assertEqual(self.q.source_path(name, "batteries"), self.baseline / (name.replace(".", "/") + ".lean"))
            for suffix in receiver.LOAD_SUFFIXES:
                relative = name.replace(".", "/") + suffix
                self.assertEqual((self.q.active / relative).read_bytes(), self.payloads[relative])
                self.assertEqual(self.q.current_artifact(name, "/old/" + relative), self.q.active / relative)
        self.assertFalse((self.q.active / "Batteries/Unrequested.olean").exists())
        record = receiver.read(self.receipt())
        self.assertEqual(record["status"], "EXACT_ORIGINAL_INPUT_BYTES_RESTORED_NOT_QUALIFICATION")
        self.assertEqual(record["selected_scope_count"], 2)
        self.assertEqual(record["module_count"], 3)
        self.assertEqual(record["facet_count"], 15)
        self.assertFalse(record["compile_credit"])
        self.assertFalse(record["kernel_credit"])

    def test_missing_facet_rejects_before_any_partial_namespace_is_created(self) -> None:
        (self.donor / ".lake/build/lib/lean/Batteries/Util/Pickle.ir.sig").unlink()
        with self.assertRaisesRegex(ValueError, "Missing Batteries donor facet"):
            self.q.restore_batteries(self.donor)
        self.assertFalse((self.q.active / "Batteries").exists())
        self.assertFalse(self.receipt().exists())

    def test_wrong_donor_bytes_cannot_restore_an_object(self) -> None:
        (self.donor / ".lake/build/lib/lean/Batteries/Tactic/Lemma.olean").write_bytes(b"wrong object")
        with self.assertRaisesRegex(ValueError, "Physical source/object/runtime differs"):
            self.q.restore_batteries(self.donor)
        self.assertFalse((self.q.active / "Batteries").exists())
        self.assertFalse(self.receipt().exists())

    def test_unrequested_shadow_object_is_rejected(self) -> None:
        path = self.q.active / "Batteries/Unrequested.olean"
        path.parent.mkdir(parents=True)
        path.write_bytes(self.payloads["Batteries/Unrequested.olean"])
        with self.assertRaisesRegex(ValueError, "Unexpected Batteries overlay file"):
            self.q.restore_batteries(self.donor)
        self.assertFalse(self.receipt().exists())

    def test_partial_overlay_cannot_be_implicitly_used_without_its_receipt(self) -> None:
        path = self.q.active / "Batteries/Tactic/Lemma.olean"
        path.parent.mkdir(parents=True)
        path.write_bytes(self.payloads["Batteries/Tactic/Lemma.olean"])
        with self.assertRaisesRegex(ValueError, "Unqualified Batteries namespace"):
            self.q.restore_batteries_if_requested(None)
        self.assertEqual(self.q.batteries_overlay, {})
        self.assertFalse(self.receipt().exists())

    def test_existing_wrong_overlay_bytes_are_not_overwritten(self) -> None:
        path = self.q.active / "Batteries/Tactic/Lemma.olean"
        path.parent.mkdir(parents=True)
        path.write_bytes(b"different existing object")
        with self.assertRaisesRegex(ValueError, "Physical source/object/runtime differs"):
            self.q.restore_batteries(self.donor)
        self.assertEqual(path.read_bytes(), b"different existing object")
        self.assertFalse(self.receipt().exists())

    def test_repeat_restoration_reuses_original_fresh_receipt_without_compilation(self) -> None:
        name = "Architect.Command"
        source = self.root / "LeanArchitect/Architect/Command.lean"
        source.parent.mkdir(parents=True)
        source.write_text("import Lean\n-- synthetic preserved fresh source\n")
        self.q.packages["LeanArchitect"] = self.root / "LeanArchitect"
        self.q.request["requested"][name] = {"package": "LeanArchitect", "source_sha256": carrier.file_sha(source),
            "git_blob_sha1": carrier.blob_sha(source.read_bytes()), "direct_imports": ["Lean"]}
        directory = self.q.stage / "qualifications/attempt-001/fresh" / name
        stem = directory / name.replace(".", "/")
        stem.parent.mkdir(parents=True)
        Path(str(stem) + ".olean").write_bytes(b"preserved fresh fixture object")
        setup, log = directory / "actual.setup.json", directory / "compile.log"
        setup.write_text('{"importArts": {}, "isModule": true}\n')
        log.write_text("synthetic successful prior process; never run in this test\n")
        active = self.q.active / "Architect/Command.olean"
        active.parent.mkdir(parents=True)
        active.write_bytes(Path(str(stem) + ".olean").read_bytes())
        receipt_path = directory / "receipt.json"
        receipt = {"status": "FRESH_PRIVATE_SOURCE_COMPILATION", "exit_code": 0, "module": name,
            "input_files_unchanged": True, "source": str(source), "source_sha256": carrier.file_sha(source),
            "command": [str(self.q.lean), "-t0", "-j1", "-M6144", "-DwarningAsError=true", str(source),
                        "-o", str(stem) + ".olean", "-i", str(stem) + ".ilean", "--setup", str(setup), "--json"],
            "cwd": str(self.q.project), "lean_path": self.q.env["LEAN_PATH"], "lean_sysroot": self.q.env["LEAN_SYSROOT"],
            "input_files": {}, "objects": {str(active): {"sha256": carrier.file_sha(active), "bytes": active.stat().st_size}},
            "log": str(log), "log_sha256": carrier.file_sha(log), "producer_script": str(self.q.producer_copy),
            "producer_script_sha256": carrier.file_sha(self.q.producer_copy), "actual_setup": str(setup),
            "actual_import_map": {}, "receipt": str(receipt_path)}
        receipt_path.write_bytes(carrier.encoded(receipt))
        with patch.object(receiver.subprocess, "run", side_effect=AssertionError("A repeat must not invoke Lean")), \
             patch.object(self.q, "freeze_core_imports") as freeze:
            self.q.restore_batteries(self.donor)
            original = self.receipt().read_bytes()
            stat = self.receipt().stat().st_mtime_ns
            # An adopter has no new CLI argument. Its initialization must
            # revalidate the persisted whole union and activate the same map.
            self.q.batteries_overlay = {}
            self.q.restore_batteries_if_requested(None)
            self.assertEqual(self.receipt().read_bytes(), original)
            self.assertEqual(self.receipt().stat().st_mtime_ns, stat)
            self.assertEqual(self.q.existing_fresh(name), receipt)
            freeze.assert_called_once_with("Lean")
        self.assertEqual(receipt_path.read_bytes(), carrier.encoded(receipt))


class CoreHeaderTests(unittest.TestCase):
    def test_actual_offending_module_header_stops_before_public_section(self) -> None:
        # Exact header of pinned Init/Meta/Defs.lean (Git blob
        # 201680de486432949cac7a2da67f00faabd021da), followed by a body that the
        # old whole-file string/comment lexer cannot safely interpret.
        text = '''/- A header comment, with /- nesting -/. -/
module
prelude
import all Init.Prelude -- for unfolding `Name.beq`
public import Init.Data.Array.Basic
public import Init.MetaTypes
import Init.Data.Array.GetLit
import Init.Data.Char.Basic
meta import Init.MetaTypes
import Init.WFTactics
public section
def quote : Char := '\\"'
import This.Is.BodyText
'''
        self.assertEqual(receiver.core_header(text), (["Init.Prelude", "Init.Data.Array.Basic", "Init.MetaTypes",
                          "Init.Data.Array.GetLit", "Init.Data.Char.Basic", "Init.WFTactics"], True))

    def test_header_without_prelude_keeps_the_implicit_init_requirement(self) -> None:
        text = '''/- A multiline
comment /- with nesting -/ ends here -/
module
public meta import all Lean.Meta.Basic
-- A comment before the first real body command.
namespace Fixture
"unterminated body string irrelevant to import parsing
'''
        self.assertEqual(receiver.core_header(text), (["Lean.Meta.Basic"], False))


if __name__ == "__main__":
    unittest.main()
