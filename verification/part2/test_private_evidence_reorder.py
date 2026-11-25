"""Transport integrity tests; fixtures provide no Lean proof credit."""
from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import unittest

import test_private_evidence_repack as original


SCRIPT = Path(__file__).with_name("reorder_winner9_private_evidence.py")


def archive_members(path):
    with tarfile.open(path, "r:xz") as archive:
        return [(member.name, archive.extractfile(member).read()) for member in archive]


def write_archive(path, members):
    with tarfile.open(path, "w:xz") as archive:
        for name, raw in members:
            item = tarfile.TarInfo(name)
            item.size = len(raw)
            archive.addfile(item, io.BytesIO(raw))


class EvidenceReorderTests(unittest.TestCase):
    def setUp(self):
        self.fixture = original.EvidenceRepackTests(
            "test_only_exact_source_duplicates_are_elided_and_every_log_is_preserved")
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.base = self.fixture.base
        self.native = [
            ("000-Z-provider.json", "/native/providers/MathlibNt.Z.json"),
            ("001-B.setup.json", "/native/MathlibNt/B.setup.json"),
            ("002-A.trace.json", "/native/MathlibNt/A.trace"),
            ("003-A.setup.json", "/native/MathlibNt/A.setup.json"),
            ("004-A-provider.json", "/native/providers/MathlibNt.A.json"),
        ]
        for label, origin in self.native:
            name = "context/native/binding/files/" + label
            raw = ('{ "origin": "' + origin + '", "escaped": "\\u03bb" }\r\n').encode()
            self.fixture.payloads[name] = raw
            self.fixture.files[name] = {
                "sha256": original.sha(raw), "bytes": len(raw), "origin": origin,
                "role": "qualified native source/provenance text; no independent proof credit"}
        with tarfile.open(self.fixture.package, "w:gz") as archive:
            data = {"PACKAGE_MANIFEST.json": json.dumps(self.fixture.package_index).encode(),
                    **self.fixture.payloads}
            for name, raw in data.items():
                item = tarfile.TarInfo(name)
                item.size = len(raw)
                archive.addfile(item, io.BytesIO(raw))
        self.fixture.manifest["packages"][0].update(
            sha256=original.sha(self.fixture.package.read_bytes()),
            bytes=self.fixture.package.stat().st_size)
        (self.fixture.export / "manifest.json").write_text(json.dumps(self.fixture.manifest))
        _, self.source, _ = self.fixture.prepare()
        self.source_bytes = self.source.read_bytes()
        self.output = self.base / "reordered.tar.xz"

    def run_tool(self, source=None, output=None, *extra):
        return subprocess.run(
            ["python3", str(SCRIPT), str(source or self.source), "--output", str(output or self.output),
             *map(str, extra)], capture_output=True, text=True)

    def test_preserves_every_member_and_still_passes_original_verifier(self):
        result = self.run_tool(None, None, "--input-sha256", original.sha(self.source_bytes))
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        before, after = archive_members(self.source), archive_members(self.output)
        self.assertEqual(dict(before), dict(after))
        self.assertEqual(self.source.read_bytes(), self.source_bytes)
        self.assertEqual(report["input"]["sha256"], original.sha(self.source_bytes))
        self.assertEqual(report["output"]["sha256"], original.sha(self.output.read_bytes()))
        self.assertEqual(report["verified_members"], len(before))
        self.assertFalse(report["proof_credit"])
        native_order = [name.rsplit("/", 1)[-1] for name, _ in after if "/native/binding/files/" in name]
        self.assertEqual(native_order, ["003-A.setup.json", "001-B.setup.json", "004-A-provider.json",
                                        "000-Z-provider.json", "002-A.trace.json"])
        verified = self.fixture.runner("verify", self.output, "--repo", self.fixture.repo)
        self.assertEqual((verified["accepted_module_count"], verified["owned_declaration_count"]), (1, 7))

    def test_rejects_changed_payload_before_publishing_output(self):
        members = archive_members(self.source)
        name, raw = members[0]
        members[0] = (name, raw + b"changed")
        corrupt = self.base / "corrupt.tar.xz"
        write_archive(corrupt, members)
        result = self.run_tool(corrupt)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("hash/size mismatch", result.stderr)
        self.assertFalse(self.output.exists())

    def test_rejects_missing_extra_duplicate_and_unsafe_members(self):
        members = archive_members(self.source)
        cases = [
            (members[1:], "inventory differs"),
            (members + [("unexpected.json", b"{}")], "inventory differs"),
            (members + [members[0]], "Duplicate member"),
            (members + [("../escape.json", b"{}")], "Unsafe member name"),
        ]
        for i, (changed, message) in enumerate(cases):
            with self.subTest(case=i):
                path = self.base / f"invalid-{i}.tar.xz"
                write_archive(path, changed)
                result = self.run_tool(path)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)
                self.assertFalse(self.output.exists())
        self.assertFalse((self.base / "escape.json").exists())

    def test_refuses_existing_output_same_input_and_dangling_symlink(self):
        self.output.write_bytes(b"keep existing output")
        result = self.run_tool()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.output.read_bytes(), b"keep existing output")
        result = self.run_tool(output=self.source)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.source.read_bytes(), self.source_bytes)
        dangling = self.base / "dangling.tar.xz"
        dangling.symlink_to(self.base / "absent-target")
        result = self.run_tool(output=dangling)
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue(dangling.is_symlink())
        self.assertFalse((self.base / "absent-target").exists())

    def test_rejects_wrong_outer_input_hash(self):
        result = self.run_tool(None, None, "--input-sha256", "0" * 64)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Input archive SHA-256 mismatch", result.stderr)
        self.assertFalse(self.output.exists())


if __name__ == "__main__":
    unittest.main()
