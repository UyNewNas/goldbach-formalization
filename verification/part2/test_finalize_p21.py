"""Synthetic export checks using published target names. No finalization or proof credit."""
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

import check_p21_joint_imports
from finalize_p21 import TARGETS, inspect_export, path_info, sha


class FinalizationSelection(unittest.TestCase):
    def setUp(self):
        repo = Path(check_p21_joint_imports.__file__).resolve().parents[2]
        self.targets = json.loads((repo / TARGETS).read_bytes())
        self.public = check_p21_joint_imports.public_targets(self.targets["roots"])
        self.native = [
            {"path": "/fixture/base", "sha256": "base-digest"},
            {"path": "/fixture/extended", "sha256": "extended-digest"},
        ]
        self.manifest = {
            "accepted_module_count": 140,
            "unselected_modules": [],
            "duplicate_owned_declarations": {},
            "owned_declaration_count": 26,
            "unique_owned_declaration_count": 26,
            "accepted_modules": {},
            "object_manifest": {},
            "files": {},
            "external_snapshots": {
                str(count): {"binding": {"native_modules": list(range(count)),
                                         "snapshot": entry["path"], "snapshot_sha256": entry["sha256"]}}
                for count, entry in zip((515, 518), self.native)
            },
        }
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        archive = Path(temp.name) / "declarations.tar.gz"
        with tarfile.open(archive, "w:gz") as tar:
            for row in self.targets["modules"]:
                owner = row["module"]
                record = {"source_sha256": row["source_sha256"], "object_sha256": "fixture-object"}
                self.manifest["object_manifest"][owner] = record
                members = []
                self.manifest["accepted_modules"][owner] = dict(record, artifact_paths=members)
                source = "sources/" + row["source"]
                self.manifest["files"][source] = {"role": "verified project source", "sha256": row["source_sha256"]}
                if owner in self.public:
                    member = "audit/" + owner + "/declarations.json"
                    members.append(member)
                    declarations = [{"name": name, "module": owner, "type": "fixture type"} for name in self.public[owner]]
                    data = json.dumps({"declarations": declarations}).encode()
                    self.manifest["files"][member] = {"role": "fixture declaration inventory", "sha256": sha(data)}
                    info = tarfile.TarInfo(member)
                    info.size = len(data)
                    tar.addfile(info, io.BytesIO(data))
        self.manifest["packages"] = [dict(path_info(archive), modules=list(self.manifest["accepted_modules"]))]

    def inspect(self):
        return inspect_export(self.manifest, self.targets, self.public, self.native)

    def test_complete_selection_returns_all_public_types(self):
        result = self.inspect()
        self.assertEqual(len(result), 26)
        self.assertEqual(result, {name: {"owner": owner, "type": "fixture type"}
                                  for owner, names in self.public.items() for name in names})

    def test_same_size_native_snapshot_with_wrong_digest(self):
        self.manifest["external_snapshots"]["515"]["binding"]["snapshot_sha256"] = "other-digest"
        with self.assertRaisesRegex(ValueError, "Unexpected native contexts"):
            self.inspect()

    def test_partial_export_missing_owner(self):
        owner = self.targets["modules"][0]["module"]
        del self.manifest["accepted_modules"][owner]
        with self.assertRaisesRegex(ValueError, "Incomplete or duplicate project coverage"):
            self.inspect()

    def test_missing_project_source_member(self):
        member = "sources/" + self.targets["modules"][0]["source"]
        del self.manifest["files"][member]
        with self.assertRaisesRegex(ValueError, "Exported project source members differ"):
            self.inspect()


if __name__ == "__main__":
    unittest.main()
