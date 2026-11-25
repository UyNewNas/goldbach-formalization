"""Synthetic regressions for the two-context compatibility gate. No Lean process."""
import copy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest

from check_p21_joint_imports import ADDED, PhysicalHashes, compatible, layout, public_targets, require_same


class JointCompatibility(unittest.TestCase):
    def test_published_manifest_requires_every_named_target(self):
        path = Path(__file__).resolve().parents[2] / "docs/verification/20261125-p2-1/TARGETS.json"
        roots = json.loads(path.read_text())["roots"]
        self.assertEqual(sum(map(len, public_targets(roots).values())), 26)
        roots[-1]["public_theorem_targets"].remove("ImbalancedChen.P2OriginalCompactQ80TableSourceOnly.sf12_contains_actual")
        with self.assertRaisesRegex(ValueError, "Public targets differ"):
            public_targets(roots)

    def test_exact_extension_preserves_all_original_bindings(self):
        modules = {"Old." + str(i): {"provider": i} for i in range(515)}
        original = {"modules": modules, "packages": {}, "resolutions": {"Old.1": "/old"},
                    "files": {"/old": {"sha256": "original"}}, "runtime": {"lean_path": ["/old"]}}
        value = copy.deepcopy(original)
        value["modules"].update(dict.fromkeys(ADDED))
        value["runtime"]["lean_path"].insert(0, "/overlay")
        base = SimpleNamespace(modules=modules, value=original)
        extended = SimpleNamespace(modules=value["modules"], value=value)
        compatible(base, extended)
        for key, name in (("modules", "Old.1"), ("resolutions", "Old.1"), ("files", "/old")):
            with self.subTest(key=key):
                saved = value[key][name]
                value[key][name] = "changed"
                with self.assertRaisesRegex(ValueError, "Extension changed a base"):
                    compatible(base, extended)
                value[key][name] = saved

    def test_physical_retarget_and_same_path_byte_mutation_are_rejected(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            package = root / "Pkg"
            package.mkdir()
            original = root / "first"
            alternate = root / "second"
            original.write_bytes(b"FIRST")
            alternate.write_bytes(b"FIRST")
            link = package / "A.olean"
            link.symlink_to(original)
            hashes = PhysicalHashes()
            files = {str(original): {"bytes": original.stat().st_size, "sha256": hashes.digest(original)}}
            value = {"resolutions": {"Pkg.A": str(original)}, "files": files}
            snap = SimpleNamespace(search_path=[root], value=value, files=files)
            layout(snap, "Pkg.A", hashes)
            legacy = SimpleNamespace(search_path=[root], value={"resolutions": {}})
            before = layout(legacy, "Pkg.A", hashes)
            original.write_bytes(b"other")
            with self.assertRaisesRegex(ValueError, "Qualified loadable facet differs"):
                layout(snap, "Pkg.A", hashes)
            with self.assertRaisesRegex(ValueError, "input changed"):
                require_same(before, layout(legacy, "Pkg.A", hashes))
            link.unlink()
            link.symlink_to(alternate)
            with self.assertRaisesRegex(ValueError, "resolved public object"):
                layout(snap, "Pkg.A", hashes)


    def test_common_unregistered_native_ir_is_rejected_in_both_views(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            base_root, overlay = root / "base", root / "overlay"
            name = "MathlibNt.A"
            package = base_root / "MathlibNt"
            package.mkdir(parents=True)
            public = package / "A.olean"
            public.write_bytes(b"qualified")
            (overlay / "MathlibNt").mkdir(parents=True)
            (overlay / "MathlibNt/A.olean").symlink_to(public)
            hashes = PhysicalHashes()
            files = {str(public): {"bytes": public.stat().st_size, "sha256": hashes.digest(public)}}
            value = {"resolutions": {name: str(public)}, "files": files}
            views = [SimpleNamespace(search_path=roots, modules={name: {}}, files=files, value=value)
                     for roots in ([base_root], [overlay, base_root])]
            self.assertEqual(layout(views[0], name, hashes), layout(views[1], name, hashes))
            extra = package / "A.ir"
            extra.write_bytes(b"unexpected")
            (overlay / "MathlibNt/A.ir").symlink_to(extra)
            for view in views:
                with self.subTest(roots=view.search_path), self.assertRaisesRegex(ValueError, "Unregistered loadable facet"):
                    layout(view, name, hashes)


if __name__ == "__main__":
    unittest.main()
