"""Focused rejection tests; only tiny synthetic archives are written."""

import copy
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

import verify_omitted_archive as v


META = Path(__file__).parent / "archive-meta"


def json_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def build_archive(path, entries, manifest=None, manifest_pin=None):
    if manifest is None:
        manifest = json_bytes({"schema": v.MANIFEST_SCHEMA, "files": {
            name: {"bytes": len(data), "sha256": v.digest(data)}
            for name, data in entries
        }})
    with tarfile.open(path, "w:xz") as archive:
        for name, data in [("FILE_MANIFEST.json", manifest), *entries]:
            member = tarfile.TarInfo(name)
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
    identity = v.hash_file(path)
    return v.Pins(identity["bytes"], identity["sha256"],
                  manifest_pin or v.digest(manifest), len(entries) + 1)


def owned_fixture():
    names = [v.MODULE + f".declaration_{i:02}" for i in range(13)]
    declarations = [{"name": name, "module": v.MODULE, "kind": "theorem",
                     "is_private": False, "type": "Nat", "type_expression": "Lean.Expr.const `Nat []",
                     "universe_parameters": [], "axioms": sorted(v.ALLOWED_AXIOMS)} for name in names]
    raw = b"MEMBER_OWNED_NAMES " + json_bytes({"names": names}) + b"\n"
    raw += b"".join(b"MEMBER_OWNED_DECL " + json_bytes(row) + b"\n" for row in declarations)
    raw += b"MEMBER_OWNED_MODULE " + json_bytes({"module": v.MODULE, "count": 13}) + b"\n"
    raw += b"MEMBER_OWNED_COUNT 13\n"
    inventory = {"schema": "member_ten_roots_complete_owned_inventory_v1",
                 "method": "Full env.constants.fold plus exact getModuleIdxFor? owner; moduleNames computed once. No private/generated exclusion.",
                 "count": 13, "names": names, "names_sha256": v.digest(("\n".join(names) + "\n").encode()),
                 "private_name_count": 0, "module_counts": {v.MODULE: 13}, "actual_audit_exit_code": 0}
    entries = [
        ("verification/full-owned.log", raw),
        ("verification/full-owned-DECLARATION_TYPES_AXIOMS.json", json_bytes(declarations)),
        ("verification/full-owned-INVENTORY_NAME_SET_CHECK.json", json_bytes(inventory)),
        ("verification/full-owned.lean", (META / "full-owned.lean").read_bytes()),
    ]
    return entries, {"inventory": inventory, "observed_axioms": sorted(v.ALLOWED_AXIOMS)}


class ArchiveValidationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name) / "test.tar.xz"

    def test_clean_tiny_archive_and_raw_audit_pass(self):
        entries, summary = owned_fixture()
        evidence = v.read_archive(self.path, build_archive(self.path, entries))
        self.assertEqual(v.verify_owned(evidence, summary)["count"], 13)

    def test_manifest_tamper_rejected_even_with_updated_archive_pin(self):
        entries = [("verification/normal-build.log", b"log\n")]
        manifest = json_bytes({"schema": v.MANIFEST_SCHEMA, "files": {
            entries[0][0]: {"bytes": 4, "sha256": v.digest(entries[0][1])}}})
        pins = build_archive(self.path, entries, manifest + b"\n", v.digest(manifest))
        with self.assertRaisesRegex(v.VerificationError, "manifest_sha256_mismatch"):
            v.read_archive(self.path, pins)

    def test_member_tamper_rejected_even_with_updated_archive_pin(self):
        name = "verification/normal-build.log"
        manifest = json_bytes({"schema": v.MANIFEST_SCHEMA, "files": {
            name: {"bytes": 4, "sha256": v.digest(b"good")}}})
        pins = build_archive(self.path, [(name, b"evil")], manifest)
        with self.assertRaisesRegex(v.VerificationError, "member_identity_mismatch"):
            v.read_archive(self.path, pins)

    def test_raw_audit_mismatch_rejected_with_self_consistent_manifest(self):
        entries, summary = owned_fixture()
        entries[0] = (entries[0][0], entries[0][1].replace(b'"type":"Nat"', b'"type":"Bool"', 1))
        evidence = v.read_archive(self.path, build_archive(self.path, entries))
        with self.assertRaisesRegex(v.VerificationError, "raw_declarations_mismatch"):
            v.verify_owned(evidence, summary)

    def test_missing_manifest_member_rejected(self):
        manifest = json_bytes({"schema": v.MANIFEST_SCHEMA, "files": {}})
        pins = build_archive(self.path, [("unlisted.txt", b"payload")], manifest)
        with self.assertRaisesRegex(v.VerificationError, "manifest_member_set_mismatch"):
            v.read_archive(self.path, pins)

    def test_duplicate_tar_paths_rejected(self):
        pins = build_archive(self.path, [("same.txt", b"a"), ("same.txt", b"a")])
        with self.assertRaisesRegex(v.VerificationError, "duplicate_tar_member"):
            v.read_archive(self.path, pins)

    def test_unsafe_tar_paths_rejected(self):
        for name in ("../escape", "/absolute", "a/../escape", "./ambiguous", "a\\escape", "C:/escape"):
            with self.subTest(name=name):
                pins = build_archive(self.path, [(name, b"data")])
                with self.assertRaisesRegex(v.VerificationError, "unsafe_member_path"):
                    v.read_archive(self.path, pins)

    def test_symlink_tar_member_rejected(self):
        with tarfile.open(self.path, "w:xz") as archive:
            member = tarfile.TarInfo("link")
            member.type = tarfile.SYMTYPE
            member.linkname = "/somewhere"
            archive.addfile(member)
        identity = v.hash_file(self.path)
        pins = v.Pins(identity["bytes"], identity["sha256"], "0" * 64, 1)
        with self.assertRaisesRegex(v.VerificationError, "unsafe_member_type"):
            v.read_archive(self.path, pins)

    def test_raw_forbidden_axiom_rejected(self):
        entries, _ = owned_fixture()
        changed = entries[0][1].replace(b'"Classical.choice"', b'"sorryAx"', 1)
        with self.assertRaisesRegex(v.VerificationError, "forbidden_axiom"):
            v.parse_owned(changed)

    def test_duplicate_json_keys_rejected(self):
        with self.assertRaisesRegex(v.VerificationError, "duplicate_json_key"):
            v.strict_json('{"exit_code":1,"exit_code":0}', "process")


class OriginalMetadataTests(unittest.TestCase):
    """Checks real small exported evidence without representing an archive PASS."""

    def test_original_owned_and_process_records_reparse(self):
        manifest = v.strict_json((META / "FILE_MANIFEST.json").read_bytes(), "manifest")
        self.assertEqual(v.digest((META / "FILE_MANIFEST.json").read_bytes()), v.Pins().manifest_sha256)
        captured = {}
        for path in META.iterdir():
            name = "verification/" + path.name
            if name in manifest["files"]:
                data = path.read_bytes()
                self.assertEqual({"bytes": len(data), "sha256": v.digest(data)}, manifest["files"][name])
                captured[name] = data
        evidence = v.Evidence(manifest["files"], captured, manifest, "FILE_MANIFEST.json", {})
        summary = evidence.json("verification/VALIDATION_RESULTS.json")
        self.assertEqual(v.verify_owned(evidence, summary)["count"], 13)
        for field, stage in (("normal", "normal-build"), ("kernel", "named-kernel"), ("owned", "full-owned")):
            self.assertEqual(v.verify_process(evidence, summary, field, stage)["exit_code"], 0)


if __name__ == "__main__":
    unittest.main()
