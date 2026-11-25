"""Synthetic transport tests only; no Lean compilation or proof credit."""
from __future__ import annotations

import copy
import gzip
import hashlib
import io
import json
import lzma
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import p27_delta_evidence as delta
import repack_winner9_private_evidence as original


def raw_json(value):
    return (json.dumps(value, sort_keys=True) + "\n").encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def tar_bytes(rows, mode="w:xz"):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode=mode) as archive:
        for name, raw in rows:
            original.add_member(archive, name, raw)
    return output.getvalue()


class DeltaTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo, self.export = self.base / "repo", self.base / "export"
        self.repo.mkdir()
        self.export.mkdir()
        self.git("init", "-q")
        self.targets_raw, self.closure_raw = delta.scope_bytes()
        self.targets = self.targets_raw.decode().splitlines()
        self.closure = json.loads(self.closure_raw)
        self.source_name = "ImbalancedChen/P2PairedCertificateCompletion.lean"
        self.source_raw = b"-- synthetic transport fixture, not a proof\n"
        p = self.repo / self.source_name
        p.parent.mkdir(parents=True)
        p.write_bytes(self.source_raw)
        self.old_member = "packages/all.tar.gz/context/native/old/files/original-setup.json"
        self.old_raw = b'{"fixture":"original actual input"}\n'
        self.old_manifest = b'{"export_schema":1,"fixture_only":true}\n'
        self.prior_payloads = {
            "ORIGINAL_EXPORT_MANIFEST.json": self.old_manifest,
            self.old_member: self.old_raw,
        }
        self.prior_slim = {
            "slim_schema": 1,
            "original_manifest_sha256": sha(self.old_manifest),
            "embedded": {n: {"sha256": sha(v), "bytes": len(v)}
                         for n, v in self.prior_payloads.items()},
            "source_references": {},
        }
        self.prior_slim_raw = raw_json(self.prior_slim)
        self.fixed = self.install_prior(self.prior_payloads)
        self.patch = patch.object(delta, "PRIOR", self.fixed)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        context_patch = patch.object(delta, "CONTEXT_ARCHIVES", [])
        context_patch.start()
        self.addCleanup(context_patch.stop)
        self.catalog = self.base / "prior-catalog.json.xz"
        self.catalog.write_bytes(lzma.compress(self.prior_slim_raw))
        self.source_catalog = self.base / "source-catalog.json"
        original.catalog(self.repo, self.source_catalog)
        self.adoption = self.base / "adoption"
        self.adoption.mkdir()
        (self.adoption / "PROJECT_CACHE_ADOPTION.json").write_bytes(
            b'{"fixture_only":true,"kernel_credit":false}\n')
        self.output = self.base / "delta.tar.xz"
        self.make_export()

    def git(self, *args, raw=False):
        out = subprocess.check_output(["git", *args], cwd=self.repo)
        return out if raw else out.decode().strip()

    def commit(self):
        self.git("add", ".")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "-qm", "fixture", "--allow-empty")
        return self.git("rev-parse", "HEAD^{tree}")

    def install_prior(self, payloads):
        raw = tar_bytes([*payloads.items(), ("SLIM_MANIFEST.json", self.prior_slim_raw)])
        pieces = [raw[:len(raw)//2], raw[len(raw)//2:]]
        parts = []
        for i, content in enumerate(pieces):
            name = f"prior/part-{i:03}.bin"
            path = self.repo / name
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(content)
            blob = sha_git(content)
            parts.append({"index": i, "path": name, "bytes": len(content),
                          "sha256": sha(content), "git_blob_sha": blob})
        index = {"schema": "p2-main-evidence-raw-parts/v1", "part_count": 2,
                 "full_archive": {"bytes": len(raw), "sha256": sha(raw)}, "parts": parts}
        index_raw = raw_json(index)
        (self.repo / "prior/index.json").write_bytes(index_raw)
        self.tree = self.commit()
        return {"history_commit": "f" * 40, "index_path": "prior/index.json",
                "index_sha256": sha(index_raw), "index_bytes": len(index_raw),
                "archive_sha256": sha(raw), "archive_bytes": len(raw), "part_count": 2,
                "slim_manifest_sha256": sha(self.prior_slim_raw),
                "original_manifest_sha256": sha(self.old_manifest)}

    def make_export(self, change=None):
        self.payloads = {
            "sources/" + self.source_name: self.source_raw,
            "context/native/new/files/current-setup.json": self.old_raw,
            "context/selected-compile-records.json": raw_json({n: {"fixture": True} for n in self.closure}),
            "context/records.json": raw_json({n: {"fixture": True} for n in self.closure}),
        }
        accepted = {}
        for n in self.targets:
            receipt = {"accepted": True, "module": n, "source_sha256": "a" * 64,
                       "object_sha256": "b" * 64, "compile_closure_signature": "c" * 64}
            name = f"audits/{n}/selected-receipt.json"
            self.payloads[name] = raw_json(receipt)
            self.payloads[f"worktree/audit/{n}/types.txt"] = b"complete fixture type\n"
            self.payloads[f"worktree/audit/{n}/replay.log"] = b"fixture replay only\n"
            accepted[n] = {k: receipt[k] for k in ("source_sha256", "object_sha256", "compile_closure_signature")}
            accepted[n].update(receipt_sha256=sha(self.payloads[name]), declaration_count=1,
                               project_modules=list(self.closure), artifact_paths=[name])
        self.manifest = {"export_schema": 1, "accepted_module_count": 26, "owned_declaration_count": 26,
                         "unique_owned_declaration_count": 26, "duplicate_owned_declarations": {},
                         "accepted_modules": accepted, "unselected_modules": [], "object_manifest": {n: {} for n in self.closure},
                         "coverage": {"geometry": {"complete": False}}, "full_p2_complete": False,
                         "worktree": str(self.base)}
        self.payloads["EXPORT_METADATA.json"] = raw_json(self.manifest)
        self.filemap = {n: {"sha256": sha(v), "bytes": len(v), "origin": "/fixture/" + n,
                           "role": "verified project source" if n.startswith("sources/") else "fixture text"}
                        for n, v in self.payloads.items()}
        package_index = {"package": "all.tar.gz", "modules": sorted(self.targets), "files": self.filemap}
        package = gzip.compress(tar_bytes([("PACKAGE_MANIFEST.json", raw_json(package_index)),
                                          *self.payloads.items()], "w"), mtime=0)
        (self.export / "all.tar.gz").write_bytes(package)
        self.manifest.update(files=self.filemap, packages=[{"path": "/fixture/all.tar.gz", "modules": sorted(self.targets),
                                                          "bytes": len(package), "sha256": sha(package)}])
        if change:
            change(self.manifest)
        (self.export / "manifest.json").write_bytes(raw_json(self.manifest))

    def pack(self):
        return delta.pack(self.export, self.source_catalog, self.catalog, self.adoption, self.output,
                          sha((self.export / "manifest.json").read_bytes()))

    def verify(self):
        return delta.verify(self.output, self.repo, self.tree, None,
                            sha((self.export / "manifest.json").read_bytes()))

    def change_delta(self, mutate):
        with tarfile.open(self.output, "r:xz") as t:
            rows = [(m.name, t.extractfile(m).read()) for m in t]
        mutate(rows)
        self.output.write_bytes(tar_bytes(rows))

    def mutate_manifest(self, mutate):
        def edit(rows):
            for i, (name, raw) in enumerate(rows):
                if name == "P27_DELTA_MANIFEST.json":
                    d = json.loads(raw)
                    mutate(d)
                    rows[i] = (name, raw_json(d))
                    return
            self.fail("delta manifest absent")
        self.change_delta(edit)

    def test_round_trip_preserves_original_metadata_and_all_new_audits(self):
        result = self.pack()
        self.assertEqual(result["prior_references"], 1)
        checked = self.verify()
        self.assertEqual((checked["accepted_module_count"], checked["project_context_count"]), (26, 81))
        self.assertEqual(checked["supplemental_files"], 1)
        self.assertFalse(checked["proof_credit"])
        with tarfile.open(self.output, "r:xz") as t:
            self.assertEqual(t.extractfile("ORIGINAL_EXPORT_MANIFEST.json").read(),
                             (self.export / "manifest.json").read_bytes())
            self.assertTrue(all("packages/all.tar.gz/audits/" + n + "/selected-receipt.json" in t.getnames()
                                for n in self.targets))

    def test_real_currentchen_staging_aliases_are_inventory_only(self):
        stem = "original-metadata/ImbalancedChen.CurrentChenBuchstabRefinement/.lake/build/"
        module = "ImbalancedChen/CurrentChenBuchstabRefinement"
        names = [stem + "lib/lean/" + module + suffix for suffix in (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")]
        names += [stem + "ir/" + module + suffix for suffix in (".c", ".c.hash", ".setup.json")]
        identities = {}
        for i, name in enumerate(names):
            p = self.adoption / name
            p.parent.mkdir(parents=True, exist_ok=True)
            target = self.base / ("facet-" + str(i))
            raw = ("synthetic facet " + name).encode()
            target.write_bytes(raw)
            identities[name] = {"sha256": sha(raw), "bytes": len(raw)}
            p.symlink_to(target)
        with patch.object(delta, "CURRENTCHEN_STAGING", identities):
            self.pack()
            result = self.verify()
        self.assertEqual(result["omitted_staging_aliases"], 8)
        with tarfile.open(self.output, "r:xz") as t:
            self.assertFalse(any("original-metadata/" in n for n in t.getnames()))

    def test_unknown_adoption_symlink_is_still_rejected(self):
        (self.adoption / "unknown.json").symlink_to(self.adoption / "PROJECT_CACHE_ADOPTION.json")
        with self.assertRaisesRegex(ValueError, "symlink|staging"):
            self.pack()
        self.assertFalse(self.output.exists())

    def test_known_staging_alias_with_wrong_target_bytes_is_rejected(self):
        for name in delta.CURRENTCHEN_STAGING:
            p = self.adoption / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.symlink_to(self.adoption / "PROJECT_CACHE_ADOPTION.json")
        with self.assertRaisesRegex(ValueError, "staging.*(SHA|bytes)|facet"):
            self.pack()
        self.assertFalse(self.output.exists())

    def test_missing_target_rejected_before_output_publication(self):
        self.make_export(lambda d: d["accepted_modules"].pop(self.targets[0]))
        with self.assertRaisesRegex(ValueError, "26|target"):
            self.pack()
        self.assertFalse(self.output.exists())

    def test_unselected_and_duplicate_owned_rejected(self):
        for key, value in (("unselected_modules", ["missing"]), ("duplicate_owned_declarations", {"name": ["a", "b"]})):
            self.make_export(lambda d: d.update({key: value}))
            with self.assertRaises(ValueError):
                self.pack()
            self.assertFalse(self.output.exists())

    def test_eighty_one_wrong_modules_do_not_pass(self):
        def change(d):
            d["object_manifest"].pop(delta.FINAL_MODULE)
            d["object_manifest"]["ImbalancedChen.Wrong"] = {}
        self.make_export(change)
        with self.assertRaisesRegex(ValueError, "81|closure"):
            self.pack()

    def test_old_catalog_tampering_is_rejected(self):
        self.catalog.write_bytes(lzma.compress(self.prior_slim_raw + b" "))
        with self.assertRaisesRegex(ValueError, "catalog|SLIM"):
            self.pack()

    def test_bad_prior_member_reference_is_rejected(self):
        self.pack()
        self.mutate_manifest(lambda d: next(iter(d["prior_references"].values())).update(member="absent.json"))
        with self.assertRaisesRegex(ValueError, "prior|member"):
            self.verify()

    def test_prior_reference_digest_is_rejected(self):
        self.pack()
        self.mutate_manifest(lambda d: next(iter(d["prior_references"].values())).update(sha256="0" * 64))
        with self.assertRaises(ValueError):
            self.verify()

    def test_missing_original_member_cannot_be_hidden_by_delta_inventory(self):
        self.pack()
        key = "packages/all.tar.gz/worktree/audit/" + self.targets[0] + "/replay.log"
        self.change_delta(lambda rows: rows.__setitem__(slice(None), [(n, v) for n, v in rows if n != key]))
        self.mutate_manifest(lambda d: d["embedded"].pop(key))
        with self.assertRaisesRegex(ValueError, "member|coverage"):
            self.verify()

    def test_extra_duplicate_and_traversal_members_rejected(self):
        self.pack()
        good = self.output.read_bytes()
        for name in ("unexpected.txt", "ORIGINAL_EXPORT_MANIFEST.json", "../escape.txt"):
            self.output.write_bytes(good)
            if name.startswith("../"):
                with tarfile.open(self.output, "r:xz") as t:
                    rows = [(m.name, t.extractfile(m).read()) for m in t]
                out = io.BytesIO()
                with tarfile.open(fileobj=out, mode="w:xz") as t:
                    for n, raw in [*rows, (name, b"bad")]:
                        m = tarfile.TarInfo(n); m.size = len(raw); t.addfile(m, io.BytesIO(raw))
                self.output.write_bytes(out.getvalue())
            else:
                self.change_delta(lambda rows: rows.append((name, b"bad")))
            with self.assertRaises(ValueError):
                self.verify()

    def test_repository_reference_reads_selected_git_tree(self):
        self.pack()
        (self.repo / self.source_name).write_bytes(b"drifted source\n")
        self.verify()  # Worktree drift must not change a frozen Git-tree lookup.
        self.tree = self.commit()
        with self.assertRaisesRegex(ValueError, "source"):
            self.verify()

    def test_changed_git_part_is_rejected(self):
        self.pack()
        p = self.repo / "prior/part-001.bin"
        p.write_bytes(p.read_bytes() + b"changed")
        self.tree = self.commit()
        with self.assertRaisesRegex(ValueError, "part|blob"):
            self.verify()

    def test_actual_prior_payload_is_hashed_not_just_the_slim_manifest(self):
        self.pack()
        bad = dict(self.prior_payloads, **{self.old_member: b"corrupted actual prior bytes\n"})
        new_fixed = self.install_prior(bad)
        self.fixed.update(new_fixed)
        # The fixed fixture archive/index now match, but its old SLIM table does not.
        self.mutate_manifest(lambda d: d.update(prior_archive=delta.prior_identity()))
        with self.assertRaisesRegex(ValueError, "prior.*(hash|member)|payload"):
            self.verify()

    def test_failed_verification_does_not_publish_report(self):
        self.pack()
        self.mutate_manifest(lambda d: d["prior_references"].clear())
        out = self.base / "success.json"
        with self.assertRaises(ValueError):
            delta.verify(self.output, self.repo, self.tree, out,
                         sha((self.export / "manifest.json").read_bytes()))
        self.assertFalse(out.exists())

    def test_receiver_rejects_object_disguised_as_supplemental_context(self):
        self.pack()
        name, raw = "supplemental/currentchen-adoption/Extra.olean", b"not text proof supply"
        self.change_delta(lambda rows: rows.append((name, raw)))
        def add(d):
            row = {"sha256": sha(raw), "bytes": len(raw), "origin": "/fixture/Extra.olean",
                   "role": "CurrentChen adoption provenance; no acceptance credit"}
            d["embedded"][name] = row
            d["supplemental"][name] = row
        self.mutate_manifest(add)
        with self.assertRaisesRegex(ValueError, "Supplemental|text"):
            self.verify()


def sha_git(raw):
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


if __name__ == "__main__":
    unittest.main()
