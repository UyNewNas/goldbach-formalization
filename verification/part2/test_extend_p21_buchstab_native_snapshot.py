"""Local synthetic checks. Run python verification/part2/test_extend_p21_buchstab_native_snapshot.py."""
import base64
import hashlib
import io
import json
import tarfile
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import extend_p21_buchstab_native_snapshot as extension


def envelope(body, name="Native.Example", line=5, **metadata):
    message = {"caption": "", "data": body, "endPos": {"column": 7, "line": line},
               "fileName": name.replace(".", "/") + ".lean", "isSilent": False, "keepFullRange": False,
               "kind": "[anonymous]", "pos": {"column": 0, "line": line}, "severity": "information"}
    message.update(metadata)
    return (json.dumps(message) + "\n").encode()


class BuchstabExtensionTests(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        task = extension.Extension.__new__(extension.Extension)
        task.casing_hashes = {}
        task.casing = None
        task.out = self.root
        task.hashes = extension.PhysicalHashes()
        task.files = {}
        task.base = SimpleNamespace(files={}, modules={}, value={"resolutions": {}}, raw_sha256="synthetic-parent")
        task.modules, task.resolutions, task.links = {}, {}, {}
        task.lib = self.root / "lib"
        task.lib.mkdir()
        task.base.search_path = [task.lib]
        task.source_roots = [self.root / "src"]
        task.pins, task.source_names, task.extra_roots = {}, {}, {}
        self.task = task

    def standard(self, name, text):
        source = self.task.source_roots[0] / extension.relative(name, ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(text)
        obj = self.task.lib / extension.relative(name, ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        obj.write_text(name)
        for p in (source, obj):
            self.task.bind(p, "fixture")
            self.task.base.files[str(p)] = self.task.files[str(p)].copy()
        self.task.base.value["resolutions"][name] = str(obj)
        return str(obj)

    def test_exact_original_header_and_no_observer_import(self):
        prefix = b"import Mathlib.Tactic\r\n\r\n"
        data = extension.probe_source(prefix + b"open Set\n", ["Mathlib.Tactic"])
        self.assertEqual(data, prefix + extension.OBSERVER)
        self.assertEqual(extension.imports(data.decode()), ["Mathlib.Tactic"])
        with self.assertRaisesRegex(ValueError, "Unsupported pinned"):
            extension.probe_source(b"public import Mathlib.Tactic\n\n", ["Mathlib.Tactic"])

    def test_inventory_checks_provider_identity_count_duplicates_and_implicit_init(self):
        names = ["Init", "Mathlib.Tactic"]
        def log(rows, count=2, main="Native.Example"):
            lines = ["P21_IMPORT " + json.dumps({"module": n, "olean": "/tmp/" + n}) for n in rows]
            lines.append("P21_HEADER " + json.dumps({"main": main, "count": count}))
            return envelope("\n".join(lines) + "\n")
        def parsed(data):
            return extension.observed(data, "Native.Example", ["Mathlib.Tactic"])
        self.assertEqual(set(parsed(log(names))), set(names))
        for data in [log(names + names), log(names, count=3), log(names, main="_stdin"),
                     log(["Init"], count=1), log(["Mathlib.Tactic"], count=1)]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                parsed(data)

    def test_only_one_information_envelope_for_the_exact_pinned_command(self):
        one = 'P21_IMPORT {"module":"Init","olean":"/Init.olean"}\n'
        body = one + 'P21_HEADER {"count":1,"main":"Native.Example"}\n'
        raw = envelope(body)
        self.assertEqual(extension.observed(raw, "Native.Example", ["Init"]), {"Init": "/Init.olean"})
        for data in [raw + raw, raw + b"\n", b"unexpected\n" + raw, body.encode(),
                     envelope(body, severity="warning"), envelope(body, line=7),
                     envelope(body, fileName="Other.lean"), envelope(body, extra=True),
                     envelope(body, isSilent=0), envelope(body, pos={"column": False, "line": 5}),
                     raw.replace(b'"data":', b'"data": "ignored", "data":'),
                     envelope(body.replace('"count":1', '"count":true')),
                     envelope(body.replace('"count":1', '"count":0,"count":1')),
                     envelope(body.replace('"module":"Init"', '"module":"Wrong","module":"Init"')),
                     envelope(body + "\n"), envelope(one + "\n" + body), envelope(body.rstrip("\n")),
                     envelope(body + one), envelope(body + "unexpected\n")]:
            with self.subTest(data=data[:120]), self.assertRaises(ValueError):
                extension.observed(data, "Native.Example", ["Init"])

    def test_only_observed_modules_credited_and_every_observed_source_and_facet_frozen(self):
        init = self.standard("Init", "prelude")
        example = self.standard("Mathlib.Example", "private import Lake.Util.Casing")
        imported = {"Init": init, "Mathlib.Example": example}
        def capture(rows):
            return self.task.inputs(rows, [self.task.lib])
        self.assertEqual(set(capture(imported)), set(imported))
        with self.assertRaisesRegex(ValueError, "No unambiguous frozen source"):
            capture(dict(imported, **{"Lake.Util.Casing": "/unqualified"}))
        with self.assertRaisesRegex(ValueError, "Missing qualified native predecessor"):
            capture({"MathlibNt.Unknown": "/unqualified"})
        with self.assertRaisesRegex(ValueError, "Observed object differs"):
            capture(dict(imported, **{"Mathlib.Example": init}))
        extra = Path(example + ".private")
        extra.write_bytes(b"not originally frozen")
        with self.assertRaisesRegex(ValueError, "Unfrozen or redirected"):
            capture(imported)
        extra.unlink()
        Path(example).write_bytes(b"changed public bytes")
        with self.assertRaisesRegex(ValueError, "changed"):
            capture(imported)

    def test_observer_uses_original_filename_cwd_and_options_and_fails_on_missing_commands(self):
        name = extension.TARGETS[0]
        source = self.root / "provider.lean"
        source.write_text("import Mathlib.Tactic\n\nexample : True := True.intro\n")
        self.task.gold, self.task.value = self.root, {"runtime": {"lean": "/pinned/lean"}}
        self.task.recheck_base = lambda: None
        env = {"LEAN_PATH": str(self.task.lib)}
        fake = subprocess.CompletedProcess([], 1, b"unknown constant Lean.findOLean")
        with patch.object(subprocess, "run", return_value=fake) as invoked:
            with self.assertRaisesRegex(ValueError, "Header inventory exit 1"):
                self.task.observe(name, source, ["Mathlib.Tactic"], [self.task.lib], env, "before")
        self.assertEqual(invoked.call_args.args[0], ["/pinned/lean", "-t0", "-j1", "-M6144",
                         "-DwarningAsError=true", "--stdin", extension.relative(name, ".lean"), "--json"])
        self.assertEqual(invoked.call_args.kwargs["cwd"], self.task.gold)
        self.assertEqual(invoked.call_args.kwargs["env"], env)
        self.assertEqual(extension.imports(invoked.call_args.kwargs["input"].decode()), ["Mathlib.Tactic"])
        self.assertFalse((self.task.out / "probes" / name / "before.log").exists())
        self.assertFalse((self.task.out / "providers" / (name + ".json")).exists())

    def test_failed_parse_or_unfrozen_input_archives_raw_without_provider_or_success_log(self):
        name = extension.TARGETS[0]
        source = self.root / "provider.lean"
        source.write_bytes(b"import Mathlib.Tactic\n\n")
        self.task.gold, self.task.value = self.root, {"runtime": {"lean": "/pinned/lean"}}
        self.task.recheck_base = lambda: None
        invalid = b'{"severity":"warning","data":"unexpected extra message"}\n'
        init = self.standard("Init", "prelude")
        tactic = self.standard("Mathlib.Tactic", "import Init")
        casing = "/unfrozen/Lake/Util/Casing.olean"
        rows = {"Init": init, "Mathlib.Tactic": tactic, "Lake.Util.Casing": casing}
        body = "".join("P21_IMPORT " + json.dumps({"module": n, "olean": path}) + "\n"
                       for n, path in rows.items())
        body += "P21_HEADER " + json.dumps({"main": name, "count": len(rows)}) + "\n"
        for phase, raw, error in [("before", invalid, "Unexpected observer message metadata"),
                                  ("after", envelope(body, name), "No unambiguous frozen source for Lake.Util.Casing")]:
            with self.subTest(phase=phase), patch.object(subprocess, "run", return_value=subprocess.CompletedProcess([], 0, raw)):
                with self.assertRaisesRegex(ValueError, error):
                    self.task.observe(name, source, ["Mathlib.Tactic"], [self.task.lib], {}, phase)
            folder = self.task.out / "probes" / name
            saved, = folder.glob(phase + "-inventory-failed-*")
            self.assertEqual(saved.read_bytes(), raw)
            self.assertFalse((folder / (phase + ".log")).exists())
            self.assertFalse((self.task.out / "providers" / (name + ".json")).exists())

    def test_existing_native_cannot_borrow_extension_facet_or_provider(self):
        name = "MathlibNt.Existing"
        obj = self.standard(name, "import Init")
        receipt = self.root / "old-receipt"
        receipt.write_text("old")
        self.task.bind(receipt, "provider")
        self.task.base.files[str(receipt)] = self.task.files[str(receipt)].copy()
        row = {"provider": {"status": "EXACT_ORIGINAL_IMPORTS_REBOUND", "receipt": str(receipt)},
               "source": str(self.task.source_roots[0] / extension.relative(name, ".lean")),
               "object": obj, "closure_signature": "original"}
        self.task.base.modules[name] = row
        self.task.modules[name] = dict(row, closure_signature="replacement")
        self.task.resolutions[name] = obj
        def capture():
            return self.task.inputs({name: obj}, [self.task.lib])
        self.assertEqual(capture()[name]["closure_signature"], "original")
        extra = Path(obj + ".private")
        extra.write_text("extension-only")
        self.task.bind(extra, "extension-output")
        with self.assertRaisesRegex(ValueError, "Unfrozen or redirected"):
            capture()
        extra.unlink()
        del self.task.base.files[str(receipt)]
        with self.assertRaisesRegex(ValueError, "lacks a qualified provider"):
            capture()

    def test_new_binding_cannot_authorize_a_missing_original_standard_resolution(self):
        obj = self.standard("Mathlib.Example", "import Init")
        del self.task.base.value["resolutions"]["Mathlib.Example"]
        self.task.resolutions["Mathlib.Example"] = obj
        with self.assertRaisesRegex(ValueError, "Unfrozen source or resolution"):
            self.task.inputs({"Mathlib.Example": obj}, [self.task.lib])

    def test_historical_casing_reuse_preserves_parent_rejects_mutation_and_redirection(self):
        # Small local archives use their own pinned publication digest, solely in the test.
        def raw(v):
            return json.dumps(v).encode()
        def sha(v):
            return hashlib.sha256(v).hexdigest()
        old = Path("/old/toolchain")
        sysroot = self.root / "toolchain"
        name = extension.CASING
        source = Path("src/lean/lake/Lake/Util/Casing.lean")
        parts = [Path("lib/lean/Lake/Util/Casing" + s) for s in extension.LOAD_SUFFIXES]
        tools = [Path(s) for s in ("bin/lake", "bin/leanchecker", "lib/lean/libleanshared.so", "lib/lean/libLake_shared.so")]
        def materialize(path):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(path.name)
            return sha(path.read_bytes())
        hashes = {str(old / rel): materialize(sysroot / rel) for rel in [source, *parts, *tools]}
        row = {"module": name, "source": str(old / source), "olean": str(old / parts[0]),
               "parts": [str(old / p) for p in parts]}
        inventory = raw({"modules": [row], "sha256": hashes})
        config = raw({"stock_tools_and_driver": {str(old / p): {"sha256": hashes[str(old / p)]} for p in tools}})
        receipt = {"returncode": 0, "scoped_gate_passed": True, "actual_imports_match_predicted_paths": True,
                   "all_import_sources_and_object_parts_unchanged": True, "runtime_config_sha256": sha(config),
                   "import_snapshot_sha256": sha(inventory), "environment": {"LEAN_SYSROOT": str(old)}}
        stem = "execution/20261012T090930892745Z-audit"
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:xz") as tar:
            for n, data in {stem + "-imports.json": inventory, stem + "-receipt.json": raw(receipt),
                            stem + "-actual-imports.json": raw([{"module": name, "olean": row["olean"]}]),
                            "runtime/runtime-config.json": config}.items():
                info = tarfile.TarInfo(n)
                info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
        archive = base64.b64encode(buf.getvalue())
        evidence = self.root / "verification/parts/p3/long-slot-normalization"
        evidence.mkdir(parents=True)
        (evidence / "local-evidence.tar.xz.b64").write_bytes(archive)
        locks = {p: materialize(self.root / p) for p in ("lean-toolchain", "lake-manifest.json")}
        published = raw({"selected_gates": {"audit": receipt}, "evidence": {"archive_base64_sha256": sha(archive)},
                         "scope_guard": {"frozen_configs_and_complete_gates": locks}})
        (evidence / "receipt.json").write_bytes(published)
        self.task.project = self.root
        self.task.value = {"runtime": {"sysroot": str(sysroot)}}
        self.task.base.raw_sha256 = extension.CASING_BASE
        self.task.base.verify = lambda: None
        roots = [self.task.lib, sysroot / "lib/lean"]
        obj = str(sysroot / parts[0])
        with patch.object(extension, "CASING_RECEIPT_SHA", sha(published)):
            self.task.casing = self.task.bind_lake_casing()
        self.assertEqual(self.task.base.files, {})
        self.assertEqual(self.task.base.value["resolutions"], {})
        self.assertEqual(self.task.modules, {})
        result = self.task.inputs({name: obj}, roots)[name]
        self.assertEqual(set(result["facets"]), set(extension.LOAD_SUFFIXES))
        self.assertEqual(result["source_sha256"], hashes[str(old / source)])
        with self.assertRaisesRegex(ValueError, "No unambiguous frozen source"):
            self.task.inputs({"Lake.Other": obj}, roots)
        with self.assertRaisesRegex(ValueError, "Observed object differs"):
            self.task.inputs({name: str(sysroot / parts[1])}, roots)
        facet = sysroot / parts[-1]
        saved = facet.read_bytes()
        facet.write_bytes(b"tamper")
        with self.assertRaisesRegex(ValueError, "Physical input changed"):
            self.task.inputs({name: obj}, roots)
        facet.unlink()
        with self.assertRaisesRegex(ValueError, "Missing qualified Casing facet"):
            self.task.inputs({name: obj}, roots)
        other = self.root / "outside"
        other.write_bytes(saved)
        facet.symlink_to(other)
        with self.assertRaisesRegex(ValueError, "Historical Casing input changed"):
            self.task.recheck_base()
        with patch.object(extension, "CASING_RECEIPT_SHA", sha(published)):
            with self.assertRaisesRegex(ValueError, "Non-canonical Casing evidence path"):
                self.task.bind_lake_casing()

    def test_batteries_overlay_recovers_only_frozen_source_in_locked_checkout(self):
        repo = self.root / "detached"
        subprocess.run(["git", "init", "-q", str(repo)], check=True)
        source = repo / "Batteries/Example.lean"
        source.parent.mkdir()
        source.write_text("import Init")
        subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
        subprocess.run(["git", "-C", str(repo), "-c", "user.name=Test", "-c", "user.email=test@local",
                        "commit", "-qm", "fixture"], check=True)
        self.task.pins["batteries"] = extension.git(repo, "rev-parse", "HEAD").decode().strip()
        self.task.source_names[source.name] = [source]
        self.task.bind(source, "fixture-source")
        self.task.base.files[str(source)] = self.task.files[str(source)].copy()
        self.assertEqual(self.task.standard_source("Batteries.Example"), source)
        self.assertIn(repo, self.task.extra_roots)

    def test_failed_candidate_does_not_publish_snapshot_or_success_marker(self):
        self.task.modules = {name: {"provider": {}} for name in extension.TARGETS}
        self.task.value = {"runtime": {"lean_path": [], "lean": "/lean"}, "context_signature": "old"}
        self.task.view = lambda _: self.root
        with patch.object(extension, "ExternalSnapshot", side_effect=ValueError("bad candidate")):
            with self.assertRaisesRegex(ValueError, "bad candidate"):
                self.task.run()
        self.assertTrue((self.root / "candidates/combined-snapshot.json").is_file())
        self.assertFalse((self.root / "EXTERNAL_SNAPSHOT.json").exists())
        self.assertFalse((self.root / "QUALIFICATION.json").exists())


if __name__ == "__main__":
    unittest.main()
