"""Lossless evidence-repack tests; fixtures provide no Lean proof credit."""
from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("repack_winner9_private_evidence.py")


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


class EvidenceRepackTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo, self.export = self.base / "repo", self.base / "export"
        self.repo.mkdir()
        self.export.mkdir()
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        for name in ("ImbalancedChen/Same.lean", "docs/source-only/old/ImbalancedChen/Same.lean"):
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"same source bytes\n")
        self.payloads = {
            "sources/ImbalancedChen/Same.lean": b"same source bytes\n",
            "sources/ImbalancedChen/Missing.lean": b"unmatched source\n",
            "worktree/audit/types.txt": b"same source bytes\n",
            "worktree/audit/replay.log": b"independent replay log\n",
            "audits/ImbalancedChen.Same/selected-receipt.json": b'{"accepted": true}\n',
        }
        self.files = {name: {"sha256": sha(raw), "bytes": len(raw), "origin": "/cloud/" + name,
                            "role": "verified project source" if name.startswith("sources/") else "accepted audit/replay artifact"}
                      for name, raw in self.payloads.items()}
        self.package = self.export / "common.tar.gz"
        self.package_index = {"package": "common.tar.gz", "modules": ["ImbalancedChen.Same"],
                              "files": self.files, "no_olean_objects": True}
        with tarfile.open(self.package, "w:gz") as archive:
            for name, raw in {"PACKAGE_MANIFEST.json": json.dumps(self.package_index).encode(), **self.payloads}.items():
                info = tarfile.TarInfo(name)
                info.size = len(raw)
                archive.addfile(info, io.BytesIO(raw))
        self.manifest = {
            "export_schema": 1, "accepted_module_count": 1, "owned_declaration_count": 7,
            "full_p2_complete": False, "coverage": {"fixture": True}, "files": self.files,
            "packages": [{"path": "/cloud/export/common.tar.gz", "sha256": sha(self.package.read_bytes()),
                          "bytes": self.package.stat().st_size, "modules": ["ImbalancedChen.Same"]}],
        }
        (self.export / "manifest.json").write_text(json.dumps(self.manifest))

    def runner(self, *args, success=True):
        result = subprocess.run(["python3", str(SCRIPT), *map(str, args)], capture_output=True, text=True)
        if success:
            self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
            return json.loads(result.stdout.strip().splitlines()[-1])
        self.assertNotEqual(result.returncode, 0)
        return result

    def prepare(self):
        catalog = self.base / "catalog.json"
        self.runner("catalog", "--repo", self.repo, "--output", catalog)
        output = self.base / "slim.tar.xz"
        result = self.runner("repack", self.export, "--catalog", catalog, "--output", output)
        return catalog, output, result

    def test_only_exact_source_duplicates_are_elided_and_every_log_is_preserved(self):
        catalog, output, result = self.prepare()
        self.assertEqual(result["source_references"], 1)
        with tarfile.open(output, "r:xz") as archive:
            slim = json.load(archive.extractfile("SLIM_MANIFEST.json"))
            self.assertEqual(slim["original_manifest_sha256"], sha((self.export / "manifest.json").read_bytes()))
            self.assertEqual(slim["original_packages"][0]["sha256"], self.manifest["packages"][0]["sha256"])
            self.assertEqual(slim["original_packages"][0]["path"], "/cloud/export/common.tar.gz")
            ref = next(iter(slim["source_references"].values()))
            self.assertEqual(len(ref["repository_paths"]), 2)
            self.assertNotIn("packages/common.tar.gz/sources/ImbalancedChen/Same.lean", archive.getnames())
            for name, raw in self.payloads.items():
                if name != "sources/ImbalancedChen/Same.lean":
                    self.assertEqual(archive.extractfile("packages/common.tar.gz/" + name).read(), raw)
        self.assertEqual(self.runner("verify", output, "--repo", self.repo)["verified_source_references"], 1)

    def test_repository_drift_makes_source_reference_unavailable(self):
        _, output, _ = self.prepare()
        for path in self.repo.rglob("*.lean"):
            path.write_text("changed\n")
        self.runner("verify", output, "--repo", self.repo, success=False)

    def test_corrupt_package_is_rejected_without_publishing_partial_output(self):
        catalog = self.base / "catalog.json"
        self.runner("catalog", "--repo", self.repo, "--output", catalog)
        with self.package.open("ab") as stream:
            stream.write(b"changed")
        output = self.base / "slim.tar.xz"
        self.runner("repack", self.export, "--catalog", catalog, "--output", output, success=False)
        self.assertFalse(output.exists())

    def test_member_payload_is_checked_even_if_outer_package_hash_is_updated(self):
        self.payloads["worktree/audit/types.txt"] = b"tampered full declaration types\n"
        with tarfile.open(self.package, "w:gz") as archive:
            for name, raw in {"PACKAGE_MANIFEST.json": json.dumps(self.package_index).encode(), **self.payloads}.items():
                info = tarfile.TarInfo(name)
                info.size = len(raw)
                archive.addfile(info, io.BytesIO(raw))
        self.manifest["packages"][0].update(sha256=sha(self.package.read_bytes()), bytes=self.package.stat().st_size)
        (self.export / "manifest.json").write_text(json.dumps(self.manifest))
        result = self.runner("inventory", self.export, "--output", self.base / "inventory.json", success=False)
        self.assertIn("Member hash/size mismatch: worktree/audit/types.txt", result.stderr)


if __name__ == "__main__":
    unittest.main()
