"""Coverage tests for new Cell01 field certificates; not a Lean verifier."""
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

import generate_scalar_decode

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
KEYS = [
    "simplex_id", "vertex_ids", "physical_volume", "mean_gap",
    "factor_maxima", "gap_weighted_means", "max_bound", "jensen_bound",
    "max_floor_Q96", "jensen_floor_Q96",
]


def check_row(source, index):
    found = re.findall(r'rawSimplex(\d+)\.getObjVal\? "([^"]+)"', source)
    expected = [(f"{index:02d}", key) for key in KEYS]
    if found != expected:
        raise ValueError("Wrong original row, key order, or field inventory")


class GeneratorBoundaryRegressions(unittest.TestCase):
    def test_scalar_generator_refuses_existing_difference_before_any_write(self):
        outputs = generate_scalar_decode.render()
        names = list(outputs)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            changed = root / names[1]
            changed.parent.mkdir(parents=True)
            changed.write_text("preserve this existing revision\n")
            with patch.object(generate_scalar_decode, "PACKAGE", root), patch.object(
                    sys, "argv", ["generate_scalar_decode.py"]):
                with self.assertRaises(SystemExit):
                    generate_scalar_decode.main()
            self.assertEqual(changed.read_text(), "preserve this existing revision\n")
            self.assertFalse((root / names[0]).exists())

    def test_row_guard_rejects_original_field_reordering(self):
        source = (ROOT / "ImbalancedChen/P2Saving16Cell01Simplex00Decode.lean").read_text()
        source = source.replace('getObjVal? "simplex_id"', 'getObjVal? "temporary"', 1)
        source = source.replace('getObjVal? "vertex_ids"', 'getObjVal? "simplex_id"', 1)
        source = source.replace('getObjVal? "temporary"', 'getObjVal? "vertex_ids"', 1)
        with self.assertRaises(ValueError):
            check_row(source, 0)

    def test_row_guard_rejects_lookup_from_a_different_original_row(self):
        source = (ROOT / "ImbalancedChen/P2Saving16Cell01Simplex00Decode.lean").read_text()
        source = source.replace("rawSimplex00.getObjVal?", "rawSimplex01.getObjVal?", 1)
        with self.assertRaises(ValueError):
            check_row(source, 0)


class FieldPackageCoverage(unittest.TestCase):
    def test_all_81_original_rows_and_ten_keys(self):
        directory = ROOT / "ImbalancedChen"
        rows = sorted(directory.glob("P2Saving16Cell01Simplex*Decode.lean"))
        self.assertEqual(len(rows), 81, "all 81 new Cell01 row decoders must exist")
        for i, path in enumerate(rows):
            self.assertEqual(path.name, f"P2Saving16Cell01Simplex{i:02d}Decode.lean")
            source = path.read_text()
            check_row(source, i)
            self.assertIn(
                f"decodeSimplex rawSimplex{i:02d} = .ok simplex{i:02d}", source)

    def test_root_fields_vertices_and_closed_composition(self):
        directory = ROOT / "ImbalancedChen"
        base = directory / "P2Saving16Cell01FieldBase.lean"
        self.assertTrue(base.exists(), "new root-field owner must exist")
        source = base.read_text()
        self.assertEqual(len(re.findall(r"^theorem lookup_", source, re.M)), 17)
        self.assertEqual(len(re.findall(r"^theorem vertex\d+_decoded", source, re.M)), 35)
        final = (directory / "P2Saving16Cell01FieldDecode.lean").read_text()
        self.assertEqual(len(re.findall(r"^import ImbalancedChen.P2Saving16Cell01Simplex", final, re.M)), 81)
        self.assertIn("decodeCell rawRoot = .ok cell01Payload", final)
        self.assertIn("decodeCell_of_field_successes rawRoot", final)

    def test_manifest_binds_existing_payload_and_generated_owners(self):
        manifest_path = ROOT / "FIELD_MANIFEST.json"
        self.assertTrue(manifest_path.exists(), "generated owner manifest must exist")
        manifest = json.loads(manifest_path.read_text())
        self.assertFalse(manifest["Lean_executed"])
        self.assertFalse(manifest["P2_5_proved"])
        for row in manifest["inputs"] + manifest["outputs"]:
            data = (REPO / row["path"]).read_bytes()
            self.assertEqual(len(data), row["bytes"])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row["sha256"])


if __name__ == "__main__":
    unittest.main()
