"""Reproduce the P3.1 source-binding and direct-build orchestration checks.

The isolated lifecycle fixture uses a deterministic fake compiler. It checks
the Python build/cache logic only. No Lean proof or axiom result is produced.
"""
from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import build_part3_pinned_closure as build
import p31_family_scale_intake as intake
import verify_part3_continuation as gate


class FamilyScaleTests(unittest.TestCase):
    def test_pinned_input_mutations(self):
        targets = gate.FAMILY_SCALE_BUDGET_MODULES

        def validate(root):
            return intake.validate_family_scale_intake(root, targets, gate.validate_project_closure)

        modules, closure, _, paths = validate(gate.ROOT)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for source in paths:
                dest = root / source.relative_to(gate.ROOT)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, dest)
            cases = [
                *(Path(m.replace(".", "/") + ".lean") for m in targets),
                Path(closure["project_sources"][0]["path"]), intake.PRIOR_CLOSURE,
                intake.DOCS / "PROJECT_IMPORT_CLOSURE.json",
                intake.DOCS / "SOURCE_INTAKE.json", intake.DOCS / "FAMILY_SCALE_PROVENANCE.json",
            ]
            for index, relative in enumerate(cases):
                with self.subTest(input=relative):
                    p = root / relative
                    initial = p.read_bytes()
                    if relative.name == "SOURCE_INTAKE.json":
                        changed = initial.replace(b'"whole_p31_complete": false',
                                                  b'"whole_p31_complete": true')
                    else:
                        changed = initial + b"\n"
                    self.assertNotEqual(initial, changed)
                    p.write_bytes(changed)
                    try:
                        with self.assertRaisesRegex(RuntimeError,
                                "source changed" if index < 3 else "digest mismatch"):
                            validate(root)
                    finally:
                        p.write_bytes(initial)
            self.assertEqual(len(validate(root)[0]), len(modules))
            self.assertEqual(len(modules), 87)

    def test_external_import_headers(self):
        source = "module\npublic import A\npublic meta import B.C\n\npublic meta section\n"
        self.assertEqual(build.external_source_imports(source, "example"), ("A", "B.C"))
        twice = "Mathlib.Algebra.Order.BigOperators.Ring.Finset"
        middle = "Mathlib.Algebra.Order.Antidiag.Nat"
        duplicate = f"import {twice}\nimport {middle}\nimport {twice}\n"
        self.assertEqual(build.external_source_imports(duplicate, "SelbergUpperBound.lean"),
                         (twice, middle))
        with self.assertRaisesRegex(RuntimeError, "Duplicate Lean import"):
            gate.source_imports(duplicate, "project.lean")
        for bad in ("module unknown\npublic import A", "module\npublic imaginary import A",
                    "import all X"):
            with self.subTest(header=bad), self.assertRaises(RuntimeError):
                build.external_source_imports(bad, "example")

    def test_isolated_direct_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sysroot = root / "toolchain"
            lean = sysroot / "bin/lean"

            def put(path, content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)

            put(lean, "#!/usr/bin/env python3\nimport hashlib, os, pathlib, sys\n"
                "if '--version' in sys.argv:\n"
                f"    print('version 4.33.0-rc1 {gate.LEAN_COMMIT}')\n"
                "elif '-o' not in sys.argv:\n"
                "    imports = pathlib.Path(sys.argv[-1]).read_text().splitlines()\n"
                "    assert set(imports) == {'import Init','import Mathlib.Example','import Vendor.Api'}\n"
                "    sys.exit(0 if pathlib.Path(os.environ['TEST_TRANSITIVE_OBJECT']).is_file() else 1)\n"
                "else:\n"
                "    out = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])\n"
                "    out.write_bytes(hashlib.sha256(pathlib.Path(sys.argv[-1]).read_bytes()).digest())\n")
            lean.chmod(0o755)
            objdir = Path(".lake/build/lib/lean")
            pkgs = {k: root / ".lake/packages" / k for k in ["goldbach", "mathlib", "LeanArchitect", "vendor"]}
            mathobj = pkgs["mathlib"] / objdir / "Mathlib/Example.olean"
            put(mathobj, "pinned external")
            put(pkgs["mathlib"] / "Mathlib/Example.lean", "")
            put(pkgs["vendor"] / "Vendor/Api.lean", "")
            put(pkgs["vendor"] / objdir / "Vendor/Api.olean", "vendor")
            for owner in ("vendor", "goldbach"):
                put(pkgs[owner] / "Collision/Api.lean", "")
            transitive = pkgs["mathlib"] / objdir / "Mathlib/Transitive.olean"
            put(transitive, "transitive external")
            put(sysroot / "lib/lean/Init.olean", "runtime")
            put(pkgs["LeanArchitect"] / "Architect.lean",
                "module\npublic import Mathlib.Example\npublic import Vendor.Api\npublic meta section\n")
            put(pkgs["goldbach"] / "MathlibNt/Example.lean", "import Architect\n")
            source = root / "ImbalancedChen/Example.lean"
            put(source, "import MathlibNt.Example\n")
            packages = []
            for name, pkg in pkgs.items():
                for args in (["init", "-q"], ["add", "."], ["-c", "user.name=Fixture", "-c",
                             "user.email=fixture@invalid.example", "commit", "--allow-empty", "-qm", "fixture"]):
                    subprocess.run(["git", *args], cwd=pkg, check=True)
                rev = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=pkg, text=True).strip()
                packages.append({"name": name, "rev": rev})
            manifest = root / "lake-manifest.json"
            put(manifest, json.dumps({"packagesDir": ".lake/packages", "packages": packages}))
            env = dict(os.environ, LEAN_SYSROOT=str(sysroot), TEST_TRANSITIVE_OBJECT=str(transitive),
                       PATH=str(sysroot / "bin") + os.pathsep + os.environ["PATH"],
                       LEAN_PATH=os.pathsep.join(str(d / objdir) for d in [root, *pkgs.values()]))

            def mock_command(*args, cwd=None):
                if args[0] == "lake":
                    return json.dumps(env)
                return subprocess.check_output(args, cwd=cwd or root, text=True).strip()

            target = "ImbalancedChen.Example"
            fixture = ((target,), {"project_sources": [
                {"module": target, "sha256": build.digest(source)}]}, None, None)

            def run(*flags):
                output = io.StringIO()
                with patch.object(sys, "argv", ["builder", "--modules", target, *flags]), \
                        contextlib.redirect_stdout(output):
                    build.main()
                return output.getvalue()

            cache = root / ".lake/receipts"
            with patch.object(build, "ROOT", root), patch.object(build, "CACHE", cache), \
                    patch.object(build, "command", mock_command), \
                    patch.object(build, "validate_family_scale_intake", return_value=fixture), \
                    patch.dict(gate.baseline.CONFIG_SHA256, {"lake-manifest.json": build.digest(manifest)}):
                # None of the rejected preflights may create compiled objects or receipts.
                for mod in ("Init", "Vendor/Api"):
                    spoof = pkgs["mathlib"] / objdir / (mod + ".olean")
                    put(spoof, "not from the owner")
                    with self.subTest(shadow=mod), self.assertRaisesRegex(RuntimeError, "shadowed"):
                        run()
                    spoof.unlink()
                for owner, rel in (("LeanArchitect", "Architect"), ("goldbach", "MathlibNt/Example")):
                    tracked = pkgs[owner] / (rel + ".lean")
                    contents = tracked.read_text()
                    tracked.unlink()
                    spoof = pkgs["mathlib"] / objdir / (rel + ".olean")
                    put(spoof, "orphaned nonowner object")
                    with self.subTest(owner=owner), self.assertRaisesRegex(RuntimeError, "tracked package source"):
                        run()
                    spoof.unlink()
                    put(tracked, contents)
                original = source.read_text()
                put(source, "import Collision.Api\n")
                fixture[1]["project_sources"][0]["sha256"] = build.digest(source)
                with self.assertRaisesRegex(RuntimeError, "unique pinned owner"):
                    run()
                put(source, original)
                fixture[1]["project_sources"][0]["sha256"] = build.digest(source)
                directory = mathobj.parent
                outside = root / "untrusted"
                directory.rename(outside)
                directory.symlink_to(outside, target_is_directory=True)
                with self.assertRaisesRegex(RuntimeError, "Invalid object part"):
                    run()
                directory.unlink()
                outside.rename(directory)
                transitive.unlink()
                with self.assertRaises(subprocess.CalledProcessError):
                    run()
                self.assertFalse((pkgs["LeanArchitect"] / objdir / "Architect.olean").exists())
                self.assertFalse(cache.exists())
                put(transitive, "transitive external")
                self.assertNotIn("COMPILE", run("--check-only"))
                self.assertFalse(cache.exists())
                self.assertEqual(run().count("COMPILE"), 3)
                self.assertEqual(run().count("REUSE"), 3)
                (cache / "MathlibNt.Example.json").unlink()
                self.assertEqual(run().count("COMPILE"), 1)
                (pkgs["goldbach"] / objdir / "MathlibNt/Example.olean").write_bytes(b"drift")
                self.assertEqual(run().count("COMPILE"), 1)
                mathobj.write_bytes(b"changed external")
                self.assertEqual(run().count("COMPILE"), 1)
                mathobj.unlink()
                with self.assertRaisesRegex(RuntimeError, "Missing or shadowed pinned external"):
                    run()


if __name__ == "__main__":
    unittest.main()
