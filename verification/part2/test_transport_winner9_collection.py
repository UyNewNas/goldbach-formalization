"""Small public-transport fixtures; these tests compile or replay no proofs."""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import stat
import tempfile
import unittest
import warnings
import zipfile


SCRIPT = Path(__file__).with_name("transport_winner9_collection.py")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class TransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # A missing implementation is an explicit RED assertion, not an import error.
        if SCRIPT.is_file():
            spec = importlib.util.spec_from_file_location("winner9_transport", SCRIPT)
            cls.module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(cls.module)
        else:
            cls.module = None

    def setUp(self):
        self.assertIsNotNone(self.module, "The public transport implementation does not exist yet")
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.archive = self.base / "source.zip"
        self.output = self.base / "delivery"
        self.bootstrap = b"existing bootstrap: must be checked but never delivered\x00\xff"
        self.plan = {"bootstrap": {"tar_sha256": sha(self.bootstrap), "run_attempt": 1,
                                    "commit": "8" * 40}}
        self.plan_sha = "e" * 64
        self.transport = {"commit": "b" * 40, "run_id": "200", "run_attempt": 3}
        self.source = {
            "repository": "UyNewNas/goldbach-formalization", "commit": "a" * 40,
            "run_id": "100", "run_attempt": 1, "artifact_id": 400,
            "artifact_name": "p210-collection-100-1", "zip_bytes": 0,
            "zip_sha256": "", "index_sha256": "",
        }
        self.payloads = {f"block-{number:02}.zip": f"original block {number:02}\n".encode() + b"\x00\xff"
                         for number in range(8, 44)}
        self.index = {
            "schema": 2, "commit": self.source["commit"], "run_id": "100", "run_attempt": "1",
            "bootstrap_origin": self.plan["bootstrap"], "bootstrap_producer_attempt": 1,
            "bootstrap_sha256": sha(self.bootstrap), "plan_sha256": self.plan_sha,
            "new_pages": 562, "new_rows": 8978,
            "old_rows_replayed": 0, "terminal_integrated": False,
        }
        self.index["blocks"] = {
            f"{number:02}": {"zip_sha256": sha(self.payloads[f"block-{number:02}.zip"]),
                              "zip_bytes": len(self.payloads[f"block-{number:02}.zip"])}
            for number in range(8, 44)
        }
        self.encode_index()
        self.payloads["bootstrap.tar.gz"] = self.bootstrap
        self.write_archive()

    def encode_index(self):
        # Deliberate whitespace must survive; the producer may not re-encode it.
        self.payloads["index.json"] = json.dumps(self.index, indent=3).encode() + b"\n\n"
        self.source["index_sha256"] = sha(self.payloads["index.json"])

    def write_archive(self, entries=None):
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with zipfile.ZipFile(self.archive, "w", compression=zipfile.ZIP_DEFLATED) as output:
                for name, raw in (entries if entries is not None else self.payloads.items()):
                    output.writestr(name, raw)
        self.source["zip_bytes"] = self.archive.stat().st_size
        self.source["zip_sha256"] = sha(self.archive.read_bytes())

    def build(self):
        return self.module.build_delivery(self.archive, self.output, self.source,
                                          self.transport, self.plan, self.plan_sha)

    def rejected(self, message):
        with self.assertRaisesRegex(ValueError, message):
            self.build()
        self.assertFalse(self.output.exists(), "Unverified source must create no delivery")

    def test_transfers_exact_original_bytes_and_omits_verified_bootstrap(self):
        original = self.archive.read_bytes()
        result = self.build()
        names = {"index.json", "tail.json", *(f"block-{number:02}.zip" for number in range(8, 44))}
        self.assertEqual({path.name for path in self.output.iterdir()}, names)
        self.assertEqual(self.archive.read_bytes(), original)
        self.assertNotIn("bootstrap.tar.gz", names)
        tail = json.loads((self.output / "tail.json").read_bytes())
        self.assertEqual(result, tail)
        self.assertEqual(set(tail), {"schema", "source", "transport", "bootstrap", "files", "scope",
                                     "proof_compilation", "stock_replay"})
        self.assertEqual(tail["schema"], "p210-public-collection-tail-v1")
        self.assertEqual(tail["source"], self.source)
        self.assertEqual(tail["transport"], {"commit": "b" * 40, "run_id": "200", "run_attempt": 3})
        self.assertEqual(tail["bootstrap"], {"filename": "bootstrap.tar.gz", "sha256": sha(self.bootstrap),
                                             "bytes": len(self.bootstrap)})
        self.assertEqual(tail["scope"], {"modules": 598, "pages": 562, "rows": 8978,
                                         "terminal_integrated": False})
        self.assertEqual(tail["proof_compilation"], 0)
        self.assertEqual(tail["stock_replay"], 0)
        self.assertEqual(set(tail["files"]), names - {"tail.json"})
        for name in names - {"tail.json"}:
            raw = (self.output / name).read_bytes()
            self.assertEqual(raw, self.payloads[name])
            self.assertEqual(tail["files"][name], {"sha256": sha(raw), "bytes": len(raw)})

    def test_rejects_wrong_complete_zip_size_or_hash(self):
        for field, wrong in (("zip_bytes", self.source["zip_bytes"] + 1), ("zip_sha256", "0" * 64)):
            with self.subTest(field=field):
                original = self.source[field]
                self.source[field] = wrong
                self.rejected("ZIP")
                self.source[field] = original

    def test_rejects_wrong_index_hash(self):
        self.source["index_sha256"] = "0" * 64
        self.rejected("index")

    def test_rejects_changed_omitted_bootstrap(self):
        self.payloads["bootstrap.tar.gz"] = b"changed bootstrap"
        self.write_archive()
        self.rejected("bootstrap")

    def test_rejects_changed_block_bytes(self):
        self.payloads["block-08.zip"] = b"X" * len(self.payloads["block-08.zip"])
        self.write_archive()
        self.rejected("block-08")

    def test_rejects_block_size_binding_mismatch(self):
        self.index["blocks"]["08"]["zip_bytes"] += 1
        self.encode_index()
        self.write_archive()
        self.rejected("block-08")

    def test_rejects_missing_duplicate_extra_and_unsafe_members(self):
        original = list(self.payloads.items())
        cases = {
            "missing": original[1:],
            "duplicate": original + [original[0]],
            "extra": original + [("unexpected.txt", b"extra")],
            "parent": original + [("../escaped.txt", b"unsafe")],
            "absolute": original + [("/absolute.txt", b"unsafe")],
            "backslash": original + [("dir\\escaped.txt", b"unsafe")],
            "directory": original + [("directory/", b"")],
        }
        for label, entries in cases.items():
            with self.subTest(label=label):
                self.write_archive(entries)
                self.rejected("member|inventory")
        self.assertFalse((self.base / "escaped.txt").exists())

    def test_rejects_symlink_even_when_its_name_is_expected(self):
        info = zipfile.ZipInfo("block-08.zip")
        info.create_system = 3
        info.external_attr = (stat.S_IFLNK | 0o777) << 16
        entries = [(info if name == "block-08.zip" else name, raw) for name, raw in self.payloads.items()]
        self.write_archive(entries)
        self.rejected("member")

    def test_rejects_wrong_index_producer_plan_or_scope(self):
        fields = (("commit", "f" * 40), ("run_id", "999"), ("run_attempt", "2"),
                  ("schema", 1), ("plan_sha256", "0" * 64), ("new_pages", 561),
                  ("new_rows", 8977), ("old_rows_replayed", 1), ("terminal_integrated", True))
        for key, wrong in fields:
            with self.subTest(field=key):
                original = self.index[key]
                self.index[key] = wrong
                self.encode_index()
                self.write_archive()
                self.rejected("index")
                self.index[key] = original

    def test_rejects_bootstrap_origin_mismatch(self):
        self.index["bootstrap_origin"] = {**self.plan["bootstrap"], "commit": "f" * 40}
        self.encode_index()
        self.write_archive()
        self.rejected("bootstrap")

    def test_refuses_existing_output_without_overwriting_it(self):
        self.output.mkdir()
        sentinel = self.output / "keep"
        sentinel.write_bytes(b"existing receiver-independent file")
        with self.assertRaisesRegex(ValueError, "exists"):
            self.build()
        self.assertEqual(sentinel.read_bytes(), b"existing receiver-independent file")
        self.assertEqual(list(self.output.iterdir()), [sentinel])

    def test_refuses_dangling_output_symlink(self):
        self.output.symlink_to(self.base / "missing")
        with self.assertRaisesRegex(ValueError, "exists"):
            self.build()
        self.assertTrue(self.output.is_symlink())
        self.assertFalse((self.base / "missing").exists())

    def test_source_metadata_binds_artifact_and_successful_proof_run(self):
        metadata = {"id": 400, "name": "p210-collection-100-1", "expired": False,
                    "size_in_bytes": self.source["zip_bytes"], "digest": "sha256:" + self.source["zip_sha256"],
                    "workflow_run": {"id": 100, "head_sha": "a" * 40}}
        run = {"id": 100, "head_sha": "a" * 40, "run_attempt": 1,
               "status": "completed", "conclusion": "success",
               "repository": {"full_name": "UyNewNas/goldbach-formalization"}}
        self.module.verify_source_metadata(metadata, run, self.source)
        cases = (("id", 401), ("name", "different-artifact"), ("expired", True),
                 ("size_in_bytes", 1), ("digest", "sha256:" + "0" * 64),
                 ("workflow_run", {"id": 999, "head_sha": "a" * 40}),
                 ("workflow_run", {"id": 100, "head_sha": "f" * 40}))
        for key, wrong in cases:
            with self.subTest(artifact_field=key):
                altered = copy.deepcopy(metadata)
                altered[key] = wrong
                with self.assertRaisesRegex(ValueError, "artifact"):
                    self.module.verify_source_metadata(altered, run, self.source)
        cases = (("id", 999), ("head_sha", "f" * 40), ("run_attempt", 2),
                 ("status", "in_progress"), ("conclusion", "failure"),
                 ("repository", {"full_name": "someone/else"}))
        for key, wrong in cases:
            with self.subTest(run_field=key):
                altered = copy.deepcopy(run)
                altered[key] = wrong
                with self.assertRaisesRegex(ValueError, "run"):
                    self.module.verify_source_metadata(metadata, altered, self.source)


if __name__ == "__main__":
    unittest.main()
