"""Focused synthetic rejection checks; no remote tools or Lean execution."""
import ast
import copy
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

import verify_nonempty_archive as v

META = Path(__file__).parent / "archive-meta"


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def make_archive(path, files, manifest=None, manifest_pin=None):
    if manifest is None:
        manifest = encoded({"schema": v.MANIFEST_SCHEMA, "files": {
            name: {"bytes": len(raw), "sha256": v.digest(raw)} for name, raw in files}})
    with tarfile.open(path, "w:xz") as archive:
        for name, raw in [("FILE_MANIFEST.json", manifest), *files]:
            member = tarfile.TarInfo(name)
            member.size = len(raw)
            archive.addfile(member, io.BytesIO(raw))
    actual = v.hash_file(path)
    return v.Pins(actual["bytes"], actual["sha256"], manifest_pin or v.digest(manifest), len(files) + 1)


def owned_fixture(count):
    names = [v.MODULE + f".decl_{i:02}" for i in range(count)]
    declarations = [{"name": name, "module": v.MODULE, "kind": "theorem", "is_private": False,
                     "type": "Nat", "type_expression": "Lean.Expr.const `Nat []", "universe_parameters": [],
                     "axioms": ["propext"]} for name in names]
    lines = [b"MEMBER_OWNED_NAMES " + encoded({"names": names})]
    lines += [b"MEMBER_OWNED_DECL " + encoded(row) for row in declarations]
    lines += [b"MEMBER_OWNED_MODULE " + encoded({"module": v.MODULE, "count": count}),
              b"MEMBER_OWNED_COUNT " + str(count).encode()]
    raw = b"\n".join(lines) + b"\n"
    inventory = {"schema": "member_ten_roots_complete_owned_inventory_v1",
                 "method": "Full env.constants.fold plus exact getModuleIdxFor? owner; moduleNames computed once. No private/generated exclusion.",
                 "count": count, "names": names, "names_sha256": v.digest(("\n".join(names) + "\n").encode()),
                 "private_name_count": 0, "module_counts": {v.MODULE: count}, "actual_audit_exit_code": 0}
    audit = (META / "full-owned.lean").read_bytes().replace(
        b"ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall", v.MODULE.encode())
    files = [("verification/full-owned.log", raw),
             ("verification/full-owned-DECLARATION_TYPES_AXIOMS.json", encoded(declarations)),
             ("verification/full-owned-INVENTORY_NAME_SET_CHECK.json", encoded(inventory)),
             ("verification/full-owned.lean", audit)]
    summary = {"owned_count": count, "inventory": inventory, "observed_axioms": ["propext"]}
    return files, summary


def graph_fixture(include_target=False):
    modules = ["Init.Prelude", "ImbalancedChen.Existing"] + ([v.MODULE] if include_target else [])
    raw_modules, parts = [], []
    for number, module in enumerate(modules):
        path = "/fixture/" + module.replace(".", "/") + ".olean"
        ident = {"path": path, "bytes": 1, "sha256": v.digest(bytes([number]))}
        raw_modules.append({"module": module, "is_module": False, "direct_imports": modules[:number],
                            "parts": [{"path": path, "resolved_path": path}]})
        parts.append({"module": module, "facet": ".olean", "identity": ident, "qualified_identity": ident.copy(),
                      "requested_path": path, "authority": "accepted", "provider": {}})
    graph = {"schema": "p29_nonempty_exact_actual_input_parts_v1", "module_count": len(modules),
             "part_count": len(parts), "actual_modules": raw_modules, "parts": parts,
             "unknown_parts": 0, "supplier_proof_replays": 0}
    raw = b"".join(b"P29_ACTUAL_IMPORT " + encoded(row) + b"\n" for row in raw_modules)
    return graph, raw


class ArchiveAndOwnedTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "fixture.tar.xz"

    def test_owned_count_is_derived_not_hardcoded(self):
        for count in (1, 4, 17):
            with self.subTest(count=count):
                files, summary = owned_fixture(count)
                evidence = v.read_archive(self.path, make_archive(self.path, files))
                self.assertEqual(v.verify_owned(evidence, summary)["count"], count)

    def test_manifest_hash_tamper_is_rejected_after_archive_repin(self):
        files = [("verification/example.log", b"ok")]
        manifest = encoded({"schema": v.MANIFEST_SCHEMA, "files": {files[0][0]: {"bytes": 2, "sha256": v.digest(b"ok")}}})
        pins = make_archive(self.path, files, manifest + b"\n", v.digest(manifest))
        with self.assertRaisesRegex(v.VerificationError, "manifest_sha256_mismatch"):
            v.read_archive(self.path, pins)

    def test_member_hash_tamper_is_rejected_after_archive_repin(self):
        name = "verification/example.log"
        manifest = encoded({"schema": v.MANIFEST_SCHEMA, "files": {name: {"bytes": 2, "sha256": v.digest(b"ok")}}})
        pins = make_archive(self.path, [(name, b"no")], manifest)
        with self.assertRaisesRegex(v.VerificationError, "member_identity_mismatch"):
            v.read_archive(self.path, pins)

    def test_raw_audit_disagreement_with_saved_records_is_rejected(self):
        files, summary = owned_fixture(4)
        files[0] = (files[0][0], files[0][1].replace(b'"type":"Nat"', b'"type":"Bool"', 1))
        evidence = v.read_archive(self.path, make_archive(self.path, files))
        with self.assertRaisesRegex(v.VerificationError, "raw_declarations_mismatch"):
            v.verify_owned(evidence, summary)

    def test_empty_inventory_and_axiom_declaration_are_rejected(self):
        files, _ = owned_fixture(0)
        with self.assertRaisesRegex(v.VerificationError, "raw_inventory_names"):
            v.parse_owned(files[0][1])
        files, _ = owned_fixture(2)
        with self.assertRaisesRegex(v.VerificationError, "unsafe_or_axiom_declaration"):
            v.parse_owned(files[0][1].replace(b'"kind":"theorem"', b'"kind":"axiom"', 1))

    def test_changed_unsafe_rejection_driver_is_rejected(self):
        files, summary = owned_fixture(2)
        files[-1] = (files[-1][0], files[-1][1].replace(b"if info.isUnsafe then", b"if false then"))
        evidence = v.read_archive(self.path, make_archive(self.path, files))
        with self.assertRaisesRegex(v.VerificationError, "pinned_member_mismatch"):
            v.verify_owned(evidence, summary)

    def test_traversal_and_duplicate_tar_paths_are_rejected(self):
        for files, error in (([("../escape", b"x")], "unsafe_member_path"),
                             ([("same", b"x"), ("same", b"x")], "duplicate_tar_member")):
            with self.subTest(error=error):
                with self.assertRaisesRegex(v.VerificationError, error):
                    v.read_archive(self.path, make_archive(self.path, files))


class GraphAndGuardTests(unittest.TestCase):
    def test_clean_graph_only_adds_target(self):
        before, before_raw = graph_fixture()
        after, after_raw = graph_fixture(True)
        v.compare_graphs(*v.graph_index(before, before_raw, "before"), *v.graph_index(after, after_raw, "after"))

    def test_old_part_byte_change_is_rejected_even_if_requalified_in_after(self):
        before, before_raw = graph_fixture()
        after, after_raw = graph_fixture(True)
        after["parts"][0]["identity"]["sha256"] = "1" * 64
        after["parts"][0]["qualified_identity"]["sha256"] = "1" * 64
        with self.assertRaisesRegex(v.VerificationError, "old_import_part_identity_changed"):
            v.compare_graphs(*v.graph_index(before, before_raw, "before"), *v.graph_index(after, after_raw, "after"))

    def test_qualified_original_bytes_cannot_change_with_relocation(self):
        graph, raw = graph_fixture()
        graph["parts"][0]["qualified_identity"]["bytes"] = 2
        with self.assertRaisesRegex(v.VerificationError, "qualified_original_bytes_changed"):
            v.graph_index(graph, raw, "before")

    def test_current_pre_post_stat_change_is_rejected(self):
        before, before_raw = graph_fixture()
        after, after_raw = graph_fixture(True)
        before["parts"][0]["stat_snapshot"] = [1, 2, 1, 4, 5]
        after["parts"][0]["stat_snapshot"] = [1, 2, 1, 4, 6]
        with self.assertRaisesRegex(v.VerificationError, "old_import_part_identity_changed"):
            v.compare_graphs(*v.graph_index(before, before_raw, "before"), *v.graph_index(after, after_raw, "after"))

    def test_import_raw_log_mismatch_is_rejected(self):
        graph, raw = graph_fixture()
        with self.assertRaisesRegex(v.VerificationError, "raw_import_modules_mismatch"):
            v.graph_index(graph, raw.replace(b'"is_module":false', b'"is_module":true', 1), "before")

    def test_guard_record_and_byte_offset_tampering_are_rejected(self):
        rows = [{"tool": "lean", "command": ["lean", "-t0", "-j2", "-M12288"]}, {"tool": "lean", "command": ["lean", "--githash"]}]
        raw = b"".join(encoded(row) + b"\n" for row in rows)
        process = {"stage": "fixture", "guard_log_start": 0, "guard_log_end": len(raw), "guarded_commands": rows}
        self.assertEqual(v.guard_slice(raw, process), rows)
        wrong = copy.deepcopy(process)
        wrong["guarded_commands"][0]["command"][3] = "-j3"
        with self.assertRaisesRegex(v.VerificationError, "guard_slice_records_mismatch"):
            v.guard_slice(raw, wrong)
        process["guard_log_start"] = 1
        with self.assertRaisesRegex(v.VerificationError, "guard_offset_line_boundary"):
            v.guard_slice(raw, process)

    def test_duplicate_json_keys_are_rejected(self):
        with self.assertRaisesRegex(v.VerificationError, "duplicate_json_key"):
            v.strict_json('{"exit_code":1,"exit_code":0}', "process")


if __name__ == "__main__":
    unittest.main()
